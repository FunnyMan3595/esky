import os
import sys
import bisect
import hashlib
import re
import stat
import urllib2
import zipfile
import shutil
import tempfile
import traceback
from collections import defaultdict
from urlparse import urlparse, urljoin
from itertools import izip_longest

from esky.finder import VersionFinder
from esky.bootstrap import parse_version, join_app_version
from esky.errors import *
from esky.util import extract_zipfile
from esky.patch import apply_patch, PatchError

class EskyDownloadError(Exception):
    def __init__(self, file):
        self.file = file
        message = "Unable to download '%s'." % file.url
        super(EskyDownloadError, self).__init__(message)

KNOWN_QUALIFIERS = {
    "pre": 0,
    "alpha": 1,
    "beta": 2,
    "rc": 3,
}

class VersionNumber(object):
    """
VersionNumber handles parsing, comparison and wildcard matching for version
numbers.


Valid version number strings can often be used in place of VersionNumber
objects.

>>> VersionNumber("1.0") == "1.0"
True
>>> "1.0" == VersionNumber("1.0")
True


Use "in" to test for a wildcard or semantic match.

>>> "1.0.3" in VersionNumber("1.*")
True
>>> "1.0.0" in VersionNumber("1")
True
>>> "1.0_pre" in VersionNumber("1.2.*")
False


== tests for an exact semantic match.

>>> "1.0.0.0" == VersionNumber("1")
True
>>> "1.2.3" == VersionNumber("1.2.3.*")
False


.in_any tests for a wildcard or semantic match to any of a set of versions.

>>> VersionNumber("1.5").in_any(["1.4", "1.5", "2.*"])
True
>>> VersionNumber("1.0").in_any(["1.*", "2.*"])
True
>>> VersionNumber("2.0").in_any(["1.*"])
False


Non-terminal wildcards are not supported.

>>> VersionNumber("1.*.3") #doctest: +ELLIPSIS
Error while parsing version number '1.*.3':
Traceback (most recent call last):
  ...
ValueError: invalid literal for int() with base 10: '*'
VersionNumber('1.*.3') (invalid)


Empty versions are valid, and match only other empty versions and empty
wildcards.

>>> "" == VersionNumber("")
True
>>> "" == VersionNumber("*")
False
>>> "" in VersionNumber("*")
True
>>> VersionNumber("").in_any(["1.*", "2.*"])
False


Qualifiers such as _pre and _rc2 are allowed.  The special qualifier _final is
ignored.

>>> "1.0_pre" == VersionNumber("1.0_pre2")
False
>>> "1.0_pre" in VersionNumber("1_*")
True
>>> "1.0_rc4" in VersionNumber("1_rc*")
True
>>> "1.0_alpha" in VersionNumber("1_rc*")
False
>>> "1.0_final" == VersionNumber("1")
True


Wildcards with qualifiers do not match versions without, and vice versa.

>>> "1.0_pre" in VersionNumber("1.*")
False
>>> "1.0" in VersionNumber("1.0_*")
False


Comparison operators may be used to compare versions.

>>> "1.0" > VersionNumber("0.5")
True
>>> "1.0_rc6" >= VersionNumber("1.0")
False
>>> "1_pre" < VersionNumber("1_alpha") < "1_beta"
True
>>> "1_beta" < VersionNumber("1_beta2") < "1_rc"
True
>>> "1_rc" < VersionNumber("1_rc4") < "1_final"
True


Comparisons using wildcards, blank version numbers, and unrecognized qualifiers
are unsupported and may raise an exception or give invalid results.

>>> "1.*" > VersionNumber("0.5") #doctest: +SKIP
???
>>> "" <= VersionNumber("2.0") #doctest: +SKIP
???
>>> "1.0_supercool" < VersionNumber("1.0") #doctest: +SKIP
???
    """
    def __init__(self, version_string):
        # Poor man's copy: get the canonical form and re-parse it.
        if isinstance(version_string, VersionNumber):
            version_string = str(version_string)

        self.invalid = False
        try:
            # Check for and remove any wildcard.
            self.wildcard = version_string.endswith("*")
            version_string = version_string.rstrip(".*")

            # If we we have nothing left, this is a blank version number.
            # (which may or may not be a wildcard)
            if not version_string:
                self.parts = []
                self.qualifier = False
                return

            # Grab any _whatever qualifier.
            # Note that _* will make has_qual true but leave qualifier blank,
            # because we stripped the trailing * earlier.
            parts = version_string.split(".")
            parts[-1], has_qual, qualifier = parts[-1].partition("_")

            # Numberify version parts.
            self.parts = map(int, parts)

            # Strip trailing .0s so that 1.0 == 1.0.0.
            # We skip this if we have a wildcard to avoid these:
            #    1.1 in 1.0.*
            #    2.0.1 in 2.0_*
            # We do *not* skip this if we have a qualifier to allow this:
            #    1.1_pre == 1.1.0_pre
            if not self.wildcard:
                while len(self.parts) > 1 and self.parts[-1] == 0:
                    self.parts.pop()

            # Handle the qualifier.
            if has_qual:
                if self.wildcard and not qualifier:
                    # Wildcard qualifier.
                    self.qualifier = True
                else:
                    # Standard qualifier.
                    self.qualifier = self.parse_qualifier(qualifier)
                    if self.qualifier and self.qualifier[1] and self.wildcard:
                        raise ValueError("Wildcard given on complete version.")
            else:
                # No qualifier.
                self.qualifier = False

        except Exception:
            # Print out a warning.  Use stdout for doctest's sake.
            print "Error while parsing version number '%s':" % version_string
            traceback.print_exc(file=sys.stdout)

            # Mark this object as invalid.
            self.invalid = True

            # Keep the string for later error messages.
            self.original_string = version_string

    def __contains__(self, other):
        if self.wildcard:
            return self.wildcard_match(other)
        else:
            return self == other

    def __eq__(self, other):
        if isinstance(other, basestring):
            # Auto-convert strings.
            other = VersionNumber(other)

        # Fail on non-version objects.
        if (not isinstance(other, VersionNumber)) or other.invalid:
            return NotImplemented
        if self.invalid:
            return NotImplemented

        # Check for an exact match.
        return (self.qualifier == other.qualifier
                and self.parts == other.parts
                and self.wildcard == other.wildcard)

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        return hash(repr(self))

    def __cmp__(self, other):
        # Comparison constants
        SELF_GREATER = 1
        EQUAL = 0
        OTHER_GREATER = -1

        if isinstance(other, basestring):
            # Auto-convert strings.
            other = VersionNumber(other)

        # Fail on non-version objects.
        if (not isinstance(other, VersionNumber)) or other.invalid:
            return NotImplemented
        if self.invalid:
            return NotImplemented

        if (not self.parts) or (not other.parts):
            raise ValueError("Can't compare empty version numbers!")

        if self.wildcard or other.wildcard:
            raise ValueError("Can't compare wildcard version numbers!")

        for mine, yours in izip_longest(self.parts, other.parts):
            if mine == None:
                return OTHER_GREATER
            elif yours == None:
                return SELF_GREATER
            elif yours > mine:
                return OTHER_GREATER
            elif mine > yours:
                return SELF_GREATER
            else:
                continue # No conclusion yet.

        # Version numbers matched, check the qualifier.
        # Versions with qualifiers are less than versions without.
        # e.g. 1.0_pre < 1.0 (== 1.0_final)
        if self.qualifier and (not other.qualifier):
            return OTHER_GREATER
        elif (not self.qualifier) and other.qualifier:
            return SELF_GREATER
        elif (not self.qualifier) and (not other.qualifier):
            return EQUAL
        else:
            # Both have a qualifier, so we have to check substance.
            my_order, my_number, my_name = self.qualifier
            your_order, your_number, your_name = other.qualifier

            if (my_order == -1) or (your_order == -1):
                raise ValueError("Can't compare unrecognized qualifiers.")
            elif my_order < your_order:
                return OTHER_GREATER
            elif your_order < my_order:
                return SELF_GREATER
            else:
                # Qualifier name matches, check number.
                if my_number < your_number:
                    return OTHER_GREATER
                elif your_number < my_number:
                    return SELF_GREATER
                else:
                    return EQUAL

    def wildcard_match(self, other):
        """
        Does this wildcard match "other"?

        Returns False if this version number is not a wildcard.

        Raises TypeError if "self" or "other" is not a valid version number.
        """
        if isinstance(other, basestring):
            # Auto-convert strings.
            other = VersionNumber(other)

        # Fail on non-version objects.
        if (not isinstance(other, VersionNumber)) or other.invalid:
            raise TypeError("Not a valid version number: %s" % other)
        if self.invalid:
            raise TypeError("Not a valid version number: %s" % self)


        # This is not a wildcard, so it does not match anything.
        # (including itself!)
        if not self.wildcard:
            return False

        # Blank wildcards match everything, including blank versions.
        if not self.parts:
            return True

        # Non-blank wildcards do not match blank versions.
        if not other.parts:
            return False

        # Non-blank wildcards without qualifiers don't match versions with them
        # and vice versa.
        if bool(other.qualifier) != bool(self.qualifier):
            return False

        # Compare the main portion of the version number.
        for mine, yours in izip_longest(self.parts, other.parts):
            if mine == None:
                if self.qualifier:
                    # 1.1_* does not match 1.1.3_alpha
                    return False
                else:
                    # 1.* matches 1.2.3
                    return True
            elif yours == None and mine != 0:
                # 1.0.0.* matches 1.0, but 1.0.1.* does not.
                return False
            elif yours != mine:
                # 1.2.* does not match 1.1.3
                return False

        # Main version numbers matched entirely.
        if not self.qualifier:
            # Neither has a qualifier, so this is an exact match for the base
            # version.  (1.1.* matches 1.1)
            return True
        elif type(self.qualifier) == bool:
            # This wildcard accepts any qualifier. (1.0_* matches 1.0_beta)
            return True
        else:
            # Do the qualifier names match?
            # 1.0_pre* matches 1.0_pre3, but not 1.0_alpha.
            name_index = 2
            return self.qualifier[name_index] == other.qualifier[name_index]

    def in_any(self, potentials):
        """Searches for this version in the given list."""
        for version in potentials:
            if isinstance(version, basestring):
                version = VersionNumber(version)

            if self in version:
                return True

        return False

    def __str__(self):
        """Returns the canonical string for this version number."""
        # For error reporting, invalid version numbers preserve the version
        # string which failed to parse.
        if self.invalid:
            return self.original_string

        # Blank wildcard.
        if self.wildcard and not self.parts:
            return "*"

        # Grab the base version number.
        version = ".".join(map(str, self.parts))

        # Add the wildcard/qualifier suffix.
        if self.wildcard and self.qualifier:
            if type(self.qualifier) == bool:
                version += "_*"
            else:
                order, number, name = self.qualifier
                version += "_%s*" % name
        elif self.wildcard:
            version += ".*"
        elif self.qualifier:
            # Reassemble, e.g., _pre6 from (0, 6, "pre")
            order, number, name = self.qualifier
            version += "_"
            version += name

            # Prefer, e.g., _pre to _pre0.
            if number != 0:
                version += str(number)

        return version

    def __repr__(self):
        message = "VersionNumber(%r)" % str(self)
        if self.invalid:
            message += " (invalid)"
        return message

    @staticmethod
    def parse_qualifier(qualifier):
        # 1.0.0_final == 1.0.0
        if qualifier == "final":
            return False

        name = qualifier.rstrip("0123456789")
        number_str = qualifier[len(name):]
        if number_str:
            number = int(number_str)
        else:
            number = 0

        qualifier_index = KNOWN_QUALIFIERS.get(name, "-1")
        return (qualifier_index, number, name)

def multiple_versions(from_version):
    versions = from_version.split(",")
    return map(VersionNumber, versions)

def hash_file(full_filename, size):
    checksum = hashlib.sha256()
    with open(full_filename, "rb+") as file:
        # Since we're doing a hash comparison, we can safely discard
        # junk data at the end of the file.  Worst that happens is the
        # hash doesn't match.
        if size != 0:
            file.truncate(size)
        data = file.read(1 * KB)
        while data:
            checksum.update(data)
            data = file.read(1 * KB)
    return checksum.hexdigest()

KB = 1024
MB = KB * 1024
class KnownFile(object):
    def __init__(self, version_finder, app_name, platform, version,
                 from_versions, url, size=0, hash=None):
        self.version_finder = version_finder
        self.app_name = app_name
        self.platform = platform
        self.version = VersionNumber(version)
        self.from_versions = multiple_versions(from_versions)
        self.url = url
        self.size = int(size)
        self.hash = hash

    def get_cost(self, app):
        full_filename = self.get_full_filename(app)

        if self.size > 0:
            # We have a size.  Use it!
            size = self.size
        elif VersionNumber("").in_any(self.from_versions):
            # Full install.  Give it a fairly high cost.
            size = 10 * MB
        else:
            # Upgrade.  Give it a fairly low cost.
            size = 2 * MB

        if self.check_hash(app):
            # No download required, so we reduce the cost drastically.
            # We still use the known/guessed filesize, because larger files
            # will take longer to install.

            # If by some strange chance we actually have an upgrade path whose
            # total size is 1/1024th as big as the already-downloaded path,
            # odds are good it'll be faster to download and install that than
            # to install the one we already have!
            return max(1, size // 1024)
        else:
            return size

    def get_filename(self):
        return os.path.basename(urlparse(self.url).path)

    def get_full_filename(self, app):
        download_dir = self.version_finder._workdir(app,"downloads")
        filename = self.get_filename()
        full_filename = os.path.join(download_dir, filename)

        return full_filename

    def check_hash(self, app, actual_size=-1, hash=None):
        full_filename = self.get_full_filename(app)

        if not os.path.exists(full_filename):
            return False

        if actual_size == -1:
            actual_size = os.path.getsize(full_filename)

        if not self.hash:
            if self.size == 0:
                # Uh.  Well, crap.  Assume it's good if there's anything there.
                return actual_size != 0
            else:
                # Size comparison is the best we can do.
                return actual_size == self.size
        else:
            # Yaaay!  Hash comparison!
            if hash == None:
                hash = hash_file(full_filename, self.size)

            return hash == self.hash

    def fetch(self, app):
        full_filename = self.get_full_filename(app)

        # Attempt to download twice before giving up.
        tries_left = 2

        # Used to avoid an infinite loop if we're stuck mid-download.
        # e.g. if the summary filesize is larger than the actual download.
        resumed_from = -1

        while tries_left > 0:
            if os.path.isfile(full_filename):
                actual_size = os.path.getsize(full_filename)
                if self.size == 0:
                    if actual_size > 0:
                        return # Assume it's good, since we can't verify.
                    else:
                        seek_to = 0
                elif actual_size < self.size:
                    seek_to = actual_size
                else:
                    if self.check_hash(app):
                        return # It's good (as far as we can tell)!
                    else:
                        # Count this as a failed download.
                        tries_left -= 1
                        os.unlink(full_filename)
            else:
                seek_to = 0

            if resumed_from == seek_to:
                # If we get stuck at the same position, count it as a failure
                # and retry from the top.
                tries_left -= 1
                resumed_from = -1
                os.unlink(full_filename)
                continue

            try:
                request = urllib2.Request(self.url)
                if seek_to > 0:
                    request.add_header("range", "bytes=%d-" % seek_to)
                    mode = "ab"
                else:
                    mode = "wb"
                resumed_from = seek_to

                # Sadly, urllib2 does not support "with".
                download = urllib2.urlopen(request)
                try:
                    with open(full_filename, mode) as file:
                        data = download.read(1 * KB)
                        while data:
                            file.write(data)
                            data = download.read(1 * KB)
                finally:
                    download.close()
            except Exception:
                traceback.print_exc()
                tries_left -= 1
                pass

        # Ran out of tries.
        raise EskyDownloadError(self)

class SummaryVersionFinder(VersionFinder):
    """
VersionFinder implementing a summary-based download scheme.

DefaultVersionFinder expects to be given the URL of a summary file, of the
following form:

    application platform version from_version URL [filesize [sha256]]
    ...

For example:
    example win32 0.1 * http://example.com/example-0.1.win32.zip
    example win32 0.2 0.1 http://example.com/example-0.1-to-0.2.win32.esky 32
    example win32 1.0 0.* http://example.com/example-0.x-to-1.0.win32.esky 1043
    example win32 1.0 * http://example.com/example-1.0.win32.zip 20004

If given, the filesize will be used to download as little data as possible.
Both filesize and sha256 will be used to check the integrity of the download.
Mixing files with and without a size is not recommended and may produce
brain-dead upgrade paths.

Consult help(VersionNumber) for information on version numbers and wildcards.

You may specify multiple from_version possibilities by separating them with a
comma, like so:
    example win32 2.3 2.0,2.1,2.1 http://example.com/example-2.x-to-2.3.win32.zip

Full-install zipfiles suitable for use with this class can be produced using
the "bdist_esky" distutils command.  Use "*" as from_version for full-install
files.

Upgrade files can be produced with esky.patch.  Consult help(esky.patch) for
more information.  Using a .esky suffix is recommended (though not required),
as these files cannot be handled by the unix "patch" command.
    """

    def __init__(self, summary_url):
        self.summary_url = summary_url
        super(SummaryVersionFinder,self).__init__()
        self.version_graph = None

    def _workdir(self,app,nm):
        """Get full path of named working directory, inside the given app."""
        workdir = os.path.join(app._get_update_dir(),nm)
        try:
            os.makedirs(workdir)
        except OSError, e:
            if e.errno not in (17,183):
                raise
        return workdir

    def identify_file(self, app, filename, file_dir):
        matches = []
        for file in self.known_files:
            if file.get_filename() == filename:
                matches.append(file)

        if not matches:
            return None
        elif len(matches) == 1:
            return matches[0]
        else:
            # Precalculate hash and size so we don't have to check again for
            # each candidate.
            full_filename = os.path.join(file_dir, filename)
            hash = hash_file(full_filename)
            size = os.path.getsize(full_filename)

            # Loop backwards, so that the last matching file is used.
            for file in matches[::-1]:
                if file.check_hash(app, size, hash):
                    return file

            # If none matched, return the most recent file and assume it's a
            # bad download.
            return matches[-1]

    def cleanup(self, app):
        # Fetch the version file.
        if not self.update_summary():
            return # Update failed!  Don't touch anything; it might explode!

        # Remove old and failed downloads.
        download_dir = self._workdir(app,"downloads")
        for filename in os.listdir(download_dir):
            file_path = os.path.join(download_dir, filename)

            # Note: I tried to implement "Is it old?" detection here, but gave
            # up due to the following issues:
            # * Is 2.0.0 immediately after 1.9.9, or is 1.15.0 between them?
            # * How do you define a "major version"?  First two parts?  1?  3?
            # * Can we logically handle 1.0.0 -> 3.0.0 and 1 -> 3 identically?
            #   VersionNumber says that 1.0.0 == 1 and 3.0.0 == 3.
            # * Is 1.9.3 from a year ago old, even if the current version is
            #   only 1.9.4?

            # Instead, I adopted the theory that when a file is so old it's
            # irrelevant, it will be removed from the summary file, even if
            # it can still be downloaded.  Problem solved.
            file = self.identify_file(app, filename, download_dir)
            if (file is None                  # Removed from summary file.
                or (not file.check_hash(app)) # Bad download.
               ):
                os.unlink(file_path)

        # Clear unpack directory.
        unpack_dir = self._workdir(app,"unpack")
        if os.path.isdir(unpack_dir):
            shutil.rmtree(unpack_dir)
        os.mkdir(unpack_dir)

        # Clear staging directory.
        ready_dir = self._workdir(app,"ready")
        if os.path.isdir(ready_dir):
            shutil.rmtree(ready_dir)
        os.mkdir(ready_dir)


    def update_summary(self):
        known_files = []
        try:
            summary = urllib2.urlopen(self.summary_url).read()
        except Exception:
            traceback.print_exc()
            return False

        for line_number, line in enumerate(summary.split("\n")):
            line = line.strip()
            if not line or line[0] == "#":
                continue

            try:
                file_info = KnownFile(self, *line.split())
                known_files.append(file_info)
            except Exception:
                print "Error handling line %d of summary file:" % line_number
                traceback.print_exc()
                # Keep going anyway.

        self.known_files = known_files
        return True

    def find_versions(self, app):
        if not self.update_summary():
            return False

        self.version_graph = SummaryVersionGraph(self.known_files, app)
        return self.version_graph.get_versions(app.version)

    def fetch_version(self, app, version):
        #  There's always the possibility that a patch fails to apply.
        #  We loop until we find a path that applies, or we run out of options.
        while True:
            # Find the best (remaining) upgrade path.
            # An exception will be raised if no path is available.
            path = self.version_graph.get_best_path(app.version,version)

            try:
                for known_file in path:
                    known_file.fetch(app)
            except EskyDownloadError, e:
                self.version_graph.remove_file(e.file)
                traceback.print_exc()
                continue

            try:
                self._prepare_version(app, version, path)
            except PatchError, e:
                self.version_graph.remove_file(e.file)
                traceback.print_exc()
                continue

            return self._get_ready_name(app, version)


    def _prepare_version(self, app, version, path):
        """Prepare the requested version from downloaded data.

        This method is responsible for unzipping downloaded versions, applying
        patches and so-forth, and making the result available as a local
        directory ready for renaming into the appdir.
        """
        if not path:
            # Current version is already prepared, or it wouldn't be running.
            return

        unpack_dir = tempfile.mkdtemp(dir=self._workdir(app, "unpack"))
        if not VersionNumber("").in_any(path[0].from_versions):
            # Upgrading from current version.
            self._copy_current_version(app, unpack_dir)
        else:
            # Clean install.
            base = path.pop(0)
            extract_zipfile(base.get_full_filename(app), unpack_dir)

        # Apply all necessary patches.
        for patch_file in path:
            full_filename = patch_file.get_full_filename(app)
            with open(full_filename, "rb") as patch:
                # If a patch fails, it'll raise an exception, which will be
                # caught outside this method.
                apply_patch(unpack_dir, patch)

        # Move anything that's not the version dir into esky-bootstrap
        version_dir = join_app_version(app.name, version, app.platform)
        bootstrap_dir = os.path.join(unpack_dir, version_dir, "esky-bootstrap")
        if not os.path.isdir(bootstrap_dir):
            os.makedirs(bootstrap_dir)
        for item in os.listdir(unpack_dir):
            if item != version_dir:
                os.rename(os.path.join(unpack_dir, item),
                          os.path.join(bootstrap_dir, item))

        # Make this version available for upgrading by moving it into ready
        # position.
        ready_dir = self._get_ready_name(app, version)
        if os.path.exists(ready_dir):
            shutil.rmtree(ready_dir)
        os.rename(os.path.join(unpack_dir, version_dir), ready_dir)

    def _copy_current_version(self, app, unpack_dir):
        # Get the current version.
        current_version = join_app_version(app.name,app.version,app.platform)
        source = os.path.join(app.appdir, current_version)

        # Copy it into place.
        shutil.copytree(source, os.path.join(unpack_dir, current_version))

        # Copy the bootstrap files.
        with open(os.path.join(source,"esky-bootstrap.txt"),"r") as manifest:
            for item in manifest:
                item = item.strip()
                bootstrap_path = os.path.join(app.appdir, item)
                dest_path = os.path.join(unpack_dir, item)

                if os.path.isdir(bootstrap_path):
                    # Copy the entire directory.
                    shutil.copytree(bootstrap_path, dest_path)
                else:
                    # We do this so that a bootstrap entry can include
                    # "data/foo.txt" but not the entirety of "data/".
                    dest_dir = os.path.dirname(dest_path)
                    if not os.path.exists(dest_dir):
                        os.makedirs(dest_dir)

                    # copy2 = copy, including metadata.
                    shutil.copy2(bootstrap_path, dest_path)

    def has_version(self, app, version):
        return os.path.exists(self._get_ready_name(app, version))

    def _get_ready_name(self,app,version):
        version = join_app_version(app.name, version, app.platform)
        return os.path.join(self._workdir(app,"ready"), version)


class SummaryVersionGraph(object):
    """
    This is an adaptation of the basic VersionGraph suitable for use with
    SummaryVersionFinder.

    As with the original, this class maintains a graph of versions and possible
    upgrades.  The internal structure has changed significantly, however,
    with KnownFile objects representing the upgrade links.
    """

    def __init__(self, known_files, app):
        self.app = app
        # {version: set(upgrade_files)}
        self.upgrades = defaultdict(set)

        self.files = set()
        self.versions = set()

        for file_info in known_files:
            if (file_info.app_name != app.name
                or file_info.platform != app.platform):
                # Not interesting to us.
                continue
            else:
                self.add_file(file_info)

    def add_file(self, new_file):
        """Add a file to the upgrade graph."""
        if new_file.version not in self.versions:
            self.new_version(new_file.version)

        self.files.add(new_file)

        for old_version in self.versions:
            if old_version > new_file.version:
                continue # Ignore downgrades.

            if old_version.in_any(new_file.from_versions):
                # Valid upgrade.
                self.upgrades[old_version].add(new_file)

    def new_version(self, version):
        self.versions.add(version)

        upgrades = self.upgrades[version] # == set(), thanks to defaultdict
        for file in self.files:
            if version.in_any(file.from_versions):
                upgrades.add(file)

    def remove_file(self, dead_file):
        """Remove a file from the upgrade graph."""
        self.files.remove(dead_file)

        # Can this version still be reached?
        version_still_exists = False
        for other_file in self.files:
            if other_file.version == dead_file.version:
                version_still_exists = True
                break

        if not version_still_exists:
            # Can't reach this version anymore; remove it.
            self.versions.remove(dead_file.version)

        # Remove this file from the upgrade sets for every version.
        for version in self.upgrades:
            try:
                self.upgrades[version].remove(dead_file)
            except KeyError:
                pass # The file couldn't upgrade this version; nothing to do.

    def get_versions(self, source):
        """List all versions reachable from the given source version."""
        current_version = VersionNumber(source)

        # Keep track of the versions we haven't reached.
        unreachable_versions = self.versions.copy()
        try:
            unreachable_versions.remove(current_version)
        except KeyError:
            # Well, that's disconcerting.  The current version isn't in the
            # summary file.
            self.new_version(current_version)

        # And the ones we've reached but not examined in detail.
        just_reached = [current_version]

        # Break out if we've examined all reachable versions,
        # or if we've reached all known versions.
        while just_reached and unreachable_versions:
            # Get the next reached but unexamined version.
            version = just_reached.pop()

            # Consider the versions we can upgrade to from this version.
            for upgrade_file in self.upgrades[version]:
                new_version = upgrade_file.version
                if new_version in unreachable_versions:
                    # If we haven't reached this version yet, we just did.
                    unreachable_versions.remove(new_version)
                    # Add it to just_reached.
                    just_reached.append(new_version)

        return self.versions - unreachable_versions


    def get_best_path(self, source, target):
        """
        Get the best path from source to target.

        This method returns a list of KnownFile objects representing the
        lowest-cost path from source to target.
        """
        source = VersionNumber(source)
        target = VersionNumber(target)

        # The following algorithm can either be described as A* with a pretty
        # dumb heuristic algorithm (h(x) = 0 for all x) or as Dijkstra's
        # algorithm with an exit condition when it reaches the target node.

        # {node: previous, file, cost, finished}
        node_status = {source: [None, None, 0, False]}

        # sorted [(cost, node)]
        queue = [(0, source)]

        while queue:
            # Grab the next-easiest node off the queue.
            cost_so_far, node = queue.pop(0)
            if node_status[node][3]:
                # Already completed this node.
                continue

            # If not, we're completing it now.
            node_status[node][3] = True

            # Since we only care about one node, we can stop when we reach it.
            if node == target:
                break

            # Use self.upgrades to determine links.
            for upgrade_file in self.upgrades[node]:
                next_node = upgrade_file.version

                # Optimization: If this version is newer than the target,
                # ignore it.
                if next_node > target:
                    continue

                # Add in the cost of this upgrade path.
                new_cost = cost_so_far + upgrade_file.get_cost(self.app)

                if next_node not in node_status:
                    # New node.  Drop it into the queue, maintaining the sort.
                    bisect.insort(queue, (new_cost, next_node))
                    node_status[next_node] = [node, upgrade_file, new_cost,
                                              False]

                previous, file, old_cost, finished = node_status[next_node]
                if (not finished) and old_cost > new_cost:
                    # Old node with improved cost.  Add it, maintain sort.
                    # Note that we leave the old version in the queue.  It will
                    # be discarded when we reach it, due to the first visit
                    # marking the node as finished.
                    bisect.insort(queue, (cost_so_far, next_node))
                    node_status[next_node] = [node, upgrade_file, cost_so_far,
                                              False]

        if target not in node_status:
            # Oops.  No valid path.
            raise EskyVersionError("No valid path from %s to %s."
                                                 % (source, target))

        # Re-assemble the path we took.
        current_node = target
        path = []
        while True:
            next_node, file, cost, finished = node_status[current_node]
            if file is None:
                break # Found the source node.
            path.append(file)
            current_node = next_node

        # Since we wrote it in reversed order, we now have to reverse the path
        # to get the correct, forwards order.
        path.reverse()

        return path


if __name__ == "__main__":
    import doctest
    doctest.testmod()
