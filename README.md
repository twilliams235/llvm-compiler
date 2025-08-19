# LLVM SWFT + CFG Pass

A small LLVM tool that adds **software fault-tolerance (SWFT)** and **checks control flow (CFG)** in an input module, then writes out the transformed bitcode and a tiny stats file.

## What it does

- **SWFT:** duplicates eligible instructions, compares original vs. clone, and calls an assert_ft(...) helper if they mismatch.

- **CFG checks:** assigns each basic block an ID and inserts checks so branches land where they should.

## Build
```LLVM_CONFIG=llvm-config```
```CXX=$($LLVM_CONFIG --cxx)```
```CXXFLAGS="$($LLVM_CONFIG --cxxflags) -O2"```
```LDFLAGS="$($LLVM_CONFIG --ldflags --libs core irreader bitreader```
```bitwriter passes analysis transformutils support)"```

```$CXX $CXXFLAGS -o swft-pass p3.cpp $LDFLAGS```

## Use
# 1) Make bitcode from C

```clang -O0 -emit-llvm -c test.c -o test.bc```

# 2) Run the pass

```./swft-pass test.bc out.bc```

# 3) Inspect results

```llvm-dis out.bc -o out.ll```
```cat out.bc.stats```


## Syntax

```./swft-pass <input.bc> <output.bc> [--verbose]```

## Output

Instrumented bitcode: out.bc

Stats CSV: out.bc.stats (e.g., counts of instrumented instructions)