/** @file Fuzzer.cpp Coverage-guided mutation of inputs supplied on stdin. */
#include <algorithm>
#include <cerrno>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <fcntl.h>
#include <map>
#include <string>
#include <sys/wait.h>
#include <unistd.h>
#include <vector>

#include "Utils.h"

namespace {

std::vector<std::string> SeedInputs;
constexpr size_t MaxGeneratedSize = 65536;
int Freq = 1000;
unsigned long Count = 0, PassCount = 0;

size_t pick(size_t Limit) { return static_cast<size_t>(rand()) % Limit; }

size_t spaceLeft(const std::string &S) {
  return MaxGeneratedSize - std::min(MaxGeneratedSize, S.size());
}

// Give short records and larger blocks a chance, regardless of seed length.
size_t blockSize() {
  size_t Base = size_t{1} << pick(10);
  return Base + pick(Base);
}

char randomByte() {
  static const char Text[] =
      "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 \t\n";
  return pick(8) == 0 ? static_cast<char>(pick(256)) : Text[pick(sizeof(Text) - 1)];
}

size_t position(size_t Count) {
  // The start and end of a token/record are often significant.
  switch (pick(8)) {
  case 0: return 0;
  case 1: return Count - 1;
  default: return pick(Count);
  }
}

std::string editByte(std::string S) {
  if (S.empty() || (spaceLeft(S) && pick(3) == 0)) {
    S.insert(position(S.size() + 1), 1, randomByte());
  } else {
    char &Byte = S[position(S.size())];
    switch (pick(3)) {
    case 0: Byte ^= 1u << pick(8); break;
    case 1: Byte = static_cast<char>(Byte + (pick(2) ? 1 : -1)); break;
    default: Byte = randomByte();
    }
  }
  return S;
}

std::string eraseBlock(std::string S) {
  if (S.empty()) return editByte(S);
  size_t N = pick(2) ? 1 : 1 + pick(S.size());
  S.erase(position(S.size() - N + 1), N);
  return S;
}

std::string writeBlock(std::string S) {
  const size_t Pos = position(S.size() + 1);
  const size_t Remove = pick(2) ? 0 : pick(S.size() - Pos + 1);
  const size_t N = std::min(blockSize(), spaceLeft(S) + Remove);
  if (!S.empty() && pick(2)) {
    const size_t Len = std::min(N, S.size());
    S.replace(Pos, Remove, S.substr(pick(S.size() - Len + 1), Len));
  } else {
    S.replace(Pos, Remove, N, randomByte());
  }
  return S;
}

// Change byte predicates without undoing length checks or record boundaries.
// Sampling the seed's own alphabet also retains its text/binary conventions.
std::string overwriteBlock(std::string S) {
  if (S.empty()) return editByte(S);
  size_t Len = pick(2) ? S.size() : 1 + pick(S.size());
  size_t Start = position(S.size() - Len + 1);
  char Byte = pick(2) ? S[pick(S.size())] : randomByte();
  for (size_t I = Start; I < Start + Len; ++I)
    if (S[I] != '\n') S[I] = Byte;
  return S;
}

// Pick a record uniformly, including an empty final record after a newline.
size_t lineStart(const std::string &S) {
  size_t Start = 0, Lines = 1;
  for (size_t I = 0; I < S.size(); ++I)
    if (S[I] == '\n' && pick(++Lines) == 0) Start = I + 1;
  return Start;
}

std::string resizeLine(std::string S) {
  size_t Start = lineStart(S);
  size_t End = S.find('\n', Start);
  size_t Old = (End == S.npos ? S.size() : End) - Start;
  size_t Len = std::min(blockSize(), Old + spaceLeft(S));
  if (pick(2)) {
    // Keep the prefix, so passing earlier character checks is not lost.
    if (Len < Old) S.erase(Start + Len, Old - Len);
    else S.insert(Start + Old, Len - Old, randomByte());
  } else {
    S.replace(Start, Old, Len, randomByte());
  }
  return S;
}

std::string editLines(std::string S) {
  size_t Start = lineStart(S);
  if (Start && pick(4) == 0) {
    S.erase(Start - 1, 1); // Join adjacent records.
  } else if (spaceLeft(S)) {
    if (pick(2)) {
      S.insert(position(S.size() + 1), 1, '\n');
    } else {
      size_t Len = std::min(blockSize(), spaceLeft(S) - 1);
      S.insert(Start, std::string(Len, randomByte()) + '\n');
    }
  }
  return S;
}

std::string editNumber(std::string S) {
  // Exercise numeric parsers with both random values and integer boundaries.
  static const char *const Boundaries[] = {
      "-1", "0", "1", "127", "128", "255", "256", "32767", "32768",
      "65535", "65536", "2147483647", "-2147483648"};
  std::string Token = pick(2) ? Boundaries[pick(sizeof(Boundaries) / sizeof(*Boundaries))]
                              : std::to_string(static_cast<int>(pick(513)) - 256);
  size_t Pos = position(S.size() + 1);
  if (Pos && S[Pos - 1] >= '0' && S[Pos - 1] <= '9') {
    Pos = S.find_last_not_of("0123456789", Pos - 1) + 1;
  }
  size_t End = S.find_first_not_of("0123456789", Pos);
  size_t Len = (End == S.npos ? S.size() : End) - Pos;
  if (Token.size() <= spaceLeft(S) + Len) S.replace(Pos, Len, Token);
  return S;
}

struct Strategy {
  std::string (*Mutate)(std::string);
  unsigned Weight = 1;
};
Strategy Strategies[] = {
    {editByte}, {eraseBlock}, {writeBlock}, {overwriteBlock},
    {resizeLine}, {editLines}, {editNumber}};

Strategy &selectMutationFn() {
  unsigned Total = 0;
  for (const auto &S : Strategies) Total += S.Weight;
  size_t Ticket = pick(Total);
  for (auto &S : Strategies) {
    if (Ticket < S.Weight) return S;
    Ticket -= S.Weight;
  }
  std::abort(); // All weights are positive.
}

const std::string &selectInput(const std::string &Last, bool LastPassed) {
  // Short random walks can cross predicates with no intermediate coverage gain.
  if (LastPassed && pick(4) == 0) return Last;
  size_t N = SeedInputs.size();
  size_t Window = pick(2) ? N : std::min<size_t>(N, 8);
  return SeedInputs[N - 1 - pick(Window)];
}

// Instrumentation emits "line, column" records. Consecutive records distinguish
// paths even when both locations were previously reached from somewhere else.
bool newCoverage(std::string &Target) {
  using Edge = std::pair<std::string, std::string>;
  static std::map<Edge, size_t> MaxBucket;
  std::map<Edge, size_t> Hits;
  std::vector<std::string> Trace;
  readCoverageFile(Target, Trace);
  std::string Prev;
  bool Novel = false;
  for (const auto &Loc : Trace) {
    Edge E{Prev, Loc};
    size_t N = ++Hits[E];
    // Reward repeat visits only at 1, 2, 4, 8, ... to avoid retaining one
    // seed per loop iteration.
    if ((N & (N - 1)) == 0 && N > MaxBucket[E]) {
      MaxBucket[E] = N;
      Novel = true;
    }
    Prev = Loc;
  }
  return Novel;
}

void feedBack(std::string &Target, const std::string &Input, bool Passed,
              Strategy &S) {
  if (Passed && newCoverage(Target)) {
    SeedInputs.push_back(Input);
    S.Weight = std::min(12u, S.Weight + 3);
  } else if (S.Weight > 1) {
    --S.Weight;
  }
}

[[noreturn]] void systemError(const char *Operation) {
  std::perror(Operation);
  std::exit(1);
}

// Use a pipe rather than the starter's fprintf("%s"): a NUL in a mutated
// input must reach the target, just as it will when a saved crash is replayed.
int runWithInput(const std::string &Target, const std::string &Input) {
  int Ends[2];
  if (pipe(Ends) < 0) systemError("pipe");
  pid_t Pid = fork();
  if (Pid < 0) systemError("fork");
  if (Pid == 0) {
    close(Ends[1]);
    int Null = open("/dev/null", O_WRONLY);
    if (dup2(Ends[0], STDIN_FILENO) < 0 || dup2(Null, STDOUT_FILENO) < 0 ||
        dup2(Null, STDERR_FILENO) < 0) _exit(127);
    close(Ends[0]);
    close(Null);
    std::signal(SIGPIPE, SIG_DFL);
    execl(Target.c_str(), Target.c_str(), static_cast<char *>(nullptr));
    _exit(127);
  }
  close(Ends[0]);
  size_t Sent = 0;
  while (Sent < Input.size()) {
    ssize_t N = write(Ends[1], Input.data() + Sent, Input.size() - Sent);
    if (N < 0) {
      if (errno == EINTR) continue;
      if (errno == EPIPE) break; // Target exited before consuming all input.
      systemError("write");
    }
    Sent += N;
  }
  close(Ends[1]);
  int Status;
  while (waitpid(Pid, &Status, 0) < 0)
    if (errno != EINTR) systemError("waitpid");
  return Status;
}

bool test(std::string &Target, std::string &Input, std::string &OutDir) {
  if (std::remove((Target + ".cov").c_str()) != 0 && errno != ENOENT)
    systemError("remove coverage file");
  int Status = runWithInput(Target, Input);
  if (WIFEXITED(Status) && WEXITSTATUS(Status) == 127) {
    std::fprintf(stderr, "Cannot launch %s; check its path and runtime libraries\n",
                 Target.c_str());
    std::exit(1);
  }
  bool Passed = WIFEXITED(Status) && WEXITSTATUS(Status) == 0;
  if (!Passed) storeCrashingInput(Input, OutDir);
  else if (PassCount++ % Freq == 0) storePassingInput(Input, OutDir);
  std::fprintf(stderr, "\rTried %lu inputs, %d crashes found", ++Count, failureCount);
  return Passed;
}

void fuzz(std::string &Target, std::string &OutDir) {
  // Calibrate coverage and record any seed which already crashes the target.
  for (auto &Seed : SeedInputs)
    if (test(Target, Seed, OutDir)) newCoverage(Target);
  std::string Last;
  bool Passed = false;
  while (true) {
    Strategy &S = selectMutationFn();
    Last = S.Mutate(selectInput(Last, Passed));
    Passed = test(Target, Last, OutDir);
    feedBack(Target, Last, Passed, S);
  }
}

} // namespace

int main(int argc, char **argv) {
  if (argc < 4 || argc > 6) {
    std::fprintf(stderr, "usage: %s TARGET SEED_DIR OUTPUT_DIR [FREQUENCY [SEED]]\n",
                 argv[0]);
    return 1;
  }
  std::string Target(argv[1]), SeedDir(argv[2]), OutDir(argv[3]);
  struct stat St;
  if (access(Target.c_str(), X_OK) != 0) systemError(Target.c_str());
  if (stat(OutDir.c_str(), &St) != 0 || !S_ISDIR(St.st_mode)) {
    std::fprintf(stderr, "Output directory not found: %s\n", OutDir.c_str());
    return 1;
  }
  if (argc >= 5) Freq = std::atoi(argv[4]);
  if (Freq <= 0) {
    std::fprintf(stderr, "Frequency must be positive\n");
    return 1;
  }
  if (readSeedInputs(SeedInputs, SeedDir)) {
    std::fprintf(stderr, "Cannot read seed directory: %s\n", SeedDir.c_str());
    return 1;
  }
  if (SeedInputs.empty()) SeedInputs.emplace_back();
  std::sort(SeedInputs.begin(), SeedInputs.end()); // Stable order for a fixed RNG seed.
  int Seed = argc == 6 ? std::atoi(argv[5]) : static_cast<int>(std::time(nullptr));
  std::srand(Seed);
  initialize(OutDir);
  storeSeed(OutDir, Seed);
  std::signal(SIGPIPE, SIG_IGN);
  std::fprintf(stderr, "Fuzzing %s...\n", Target.c_str());
  fuzz(Target, OutDir);
}
