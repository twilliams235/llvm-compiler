#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <set>
#include <vector>
#include <utility>
#include <iostream>

#include "llvm-c/Core.h"

#include "llvm/IR/CFG.h"
#include "llvm/ADT/iterator_range.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/IR/PassManager.h"
//#include "llvm/Analysis/CGSCCAnalysisManager.h"
//#include "llvm/Analysis/ModuleAnalysisManager.h"


using namespace llvm;

static LLVMContext Context;

void replicate(Function* f, Module *M);
bool canRep(Instruction &I);
void verifyControlFlow(Function* f, Module *M);
bool isUndefOrPoison(Instruction &I);


LLVMContext& getGlobalContext() {
  return Context;
}


static void SoftwareFaultTolerance(Module *);

static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        NoSWFT("no-swft",
              cl::desc("Do not perform SWFT."),
              cl::init(false));


static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));

// Use this to enable your bonus code
static cl::opt<bool>
        Bonus("bonus",
                cl::desc("Run the bonus code."),
                cl::init(false));

// Use these to control whether or not parts of your pass run
static cl::opt<bool>
        NoReplicate("no-replicate",
              cl::desc("Do not perform code replication."),
              cl::init(false));

static cl::opt<bool>
        NoControlProtection("no-control-protection",
              cl::desc("Do not perform control flow protection."),
              cl::init(false));



void RunO2(Module *M);
void BuildHelperFunctions(Module *);
void summarize(Module *M);
FunctionCallee AssertFT;
FunctionCallee AssertCFG;

int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

    // LLVM idiom for constructing output file.
    std::unique_ptr<ToolOutputFile> Out;
    std::string ErrorInfo;
    std::error_code EC;
    Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                                 sys::fs::OF_None));

    EnableStatistics();

    // Read in module
    SMDiagnostic Err;
    std::unique_ptr<Module> M;
    M = parseIRFile(InputFilename, Err, Context);

    // If errors, fail
    if (M.get() == 0)
    {
        Err.print(argv[0], errs());
        return 1;
    }

    // Run O2 optimizations
    RunO2(M.get());

    BuildHelperFunctions(M.get());      
    
    if (!NoSWFT) {
      SoftwareFaultTolerance(M.get());
    }

    // Collect statistics on Module
    summarize(M.get());
    print_csv_file(OutputFilename);

    if (Verbose)
        PrintStatistics(errs());

    // Verify integrity of Module, do this by default
    if (!NoCheck)
    {
        legacy::PassManager Passes;
        Passes.add(createVerifierPass());
        Passes.run(*M.get());
    }

    // Write final bitcode
    WriteBitcodeToFile(*M.get(), Out->os());
    Out->keep();

    return 0;
}

static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}

// Collect this statistic; increment for each instruction you add.
static llvm::Statistic SWFTAdded = {"", "SWFTadd", "SWFT added instructions"};



static void SoftwareFaultTolerance(Module *M) {
  Module::FunctionListType &list = M->getFunctionList();

  std::vector<Function*> flist;
  // FIND THE ASSERT FUNCTIONS AND DO NOT INSTRUMENT THEM
  for(Module::FunctionListType::iterator it = list.begin(); it!=list.end(); it++) {
    Function *fptr = &*it;
    if (fptr->size() > 0 && fptr != AssertFT.getCallee() && fptr != AssertCFG.getCallee())
      flist.push_back(fptr);
  }

  // PROTECT CODE IN EACH FUNCTION
  for(std::vector<Function*>::iterator it=flist.begin(); it!=flist.end(); it++)
    {
      replicate(*it, M);
      verifyControlFlow(*it, M);
    }
}

// Control Flow Verification Pass
void verifyControlFlow(Function* f, Module *M) {
  int bbCount = 0;
  int iCount;
  int uniqueID;
  int isEntryBlock = 1;     // Flag to account for the entry block to every function
  std::unordered_map<BasicBlock*, unsigned int> idMap = {};   //map for unique ids of basic blocks
  std::unordered_map<BasicBlock*, Value*> diffMap = {};   //map for basicblocks and their diff value
  std::unordered_map<BasicBlock*, Value*> destMap = {}; //map for basicblocks and their dest value
  std::unordered_map<BasicBlock*, PHINode*> destPhiMap = {};    //map for basicblocks and their diff phi node
  std::unordered_map<BasicBlock*, PHINode*> diffPhiMap = {};    //map for basicblocks and their dest phi node

  // Loop to fill the unique ID map
  for(auto bb=(*f).begin();bb!=(*f).end();bb++) {
    BasicBlock& block = *bb;    //get the basic block
    bbCount++;      //increment the bb count
    iCount = std::distance(bb->begin(),bb->end());

    //compute unique ID
    uniqueID = ((bbCount << 20) | (iCount << 8) |  ((bbCount*iCount) % 37));
    
    // store this unique id as a pair for the basicblock its in
    idMap[&block] = uniqueID;
  }


  // Loop to build phi nodes and call assert_cfg_ft, as well as calulate new diff and new dest
  for(auto bb=(*f).begin();bb!=(*f).end();bb++) {
    BasicBlock& block = *bb;    //get the basic block  
    Instruction& first = *block.getFirstNonPHI();
    BasicBlock::iterator begin(first); 
    
    // If not an entry block
    if(isEntryBlock == 0) {
      IRBuilder<> Builder(&*begin);        //Insert builder after last phi

      //Create Diff and Dest phis without their operands
      PHINode *Diff = Builder.CreatePHI(Type::getInt32Ty(getGlobalContext()), 0, "Diff");
      PHINode *Dest = Builder.CreatePHI(Type::getInt32Ty(getGlobalContext()), 0, "Dest");

      //Insert into phi maps
      diffPhiMap[&block] = Diff;
      destPhiMap[&block] = Dest;

      // Convert from PHINode to Value
      Value* diffVal = dyn_cast<Value>(Diff);
      Value* destVal = dyn_cast<Value>(Dest);

      // Compute Diff xor Dest
      Value* xorDest = Builder.CreateXor(diffVal, destVal, "DestX");

      // Compute icmp of XORed value and block's unique ID
      Value *cfgCmp = Builder.CreateICmpEQ(xorDest, Builder.getInt32(idMap[&block]), "cfgCmp");

      // Zero extend icmp value
      Value *zext = Builder.CreateZExt(cfgCmp, Type::getInt32Ty(getGlobalContext()), "cfgZext");

      std::vector<Value*> args;
      args.push_back(zext); // boolean
      args.push_back(Dest);
      args.push_back(Builder.getInt32(idMap[&block])); // unique id
      Function *F = M->getFunction("assert_cfg_ft");
      Builder.CreateCall(F->getFunctionType(), F, args);    //create call to assert_cfg_ft

      //Find the terminator of the Basic Block to see if it is a branch
      Instruction *terminator = block.getTerminator();
      BasicBlock::iterator it2(terminator);
      IRBuilder<> Builder1(&*it2);        // Insert builder above terminator

      // Check if the terminator is a conditional branch
      if (isa<BranchInst>(terminator)) {
        BranchInst *branchInst = dyn_cast<BranchInst>(terminator);
        if (branchInst->isConditional()) {
          // If it's a conditional branch, use select instruction to choose the correct destination block ID
          // Get the condition
          // Create select instruction
          Value *selectedDest = Builder1.CreateSelect(branchInst->getCondition(), Builder1.getInt32(idMap[branchInst->getSuccessor(0)]), Builder1.getInt32(idMap[branchInst->getSuccessor(1)]), "select"); //How do I make this produce an i32

          // Compute the new Diff by current block ID xor destination block ID
          Value *newDiff = Builder1.CreateXor(Builder1.getInt32(idMap[&block]), selectedDest, "xorDiff");

          // Store the new Diff in diffMap
          if(diffMap.find(&block) == diffMap.end())
            diffMap[&block] = newDiff;

          // Store the destination block ID in destMap
          if(destMap.find(&block) == destMap.end())
            destMap[&block] = xorDest;
        }
        else {
          Value *newDiff = Builder1.CreateXor(Builder1.getInt32(idMap[&block]), Builder1.getInt32(idMap[branchInst->getSuccessor(0)]), "xorDiff");

          // Store the new Diff in diffMap
          if(diffMap.find(&block) == diffMap.end())
            diffMap[&block] = newDiff;

          // Store the destination block ID in destMap
          if(destMap.find(&block) == destMap.end())
            destMap[&block] = xorDest;
        }
      } else if(terminator->getNumSuccessors() > 0) {
        Value *newDest = Builder1.getInt32(idMap[&block]);
        Value *newDiff = Builder1.CreateXor(Builder1.getInt32(idMap[&block]), Builder1.getInt32(idMap[terminator->getSuccessor(0)]), "xorDiff");

        // Store the new Diff in diffMap
        diffMap[&block] = newDiff;

        // Store the destination block ID in destMap
        destMap[&block] = newDest;
      }
    }
    // else is an entry block
    else {
      isEntryBlock = 0;
      Instruction *terminator = block.getTerminator();
      BasicBlock::iterator it(terminator);
      IRBuilder<> Builder2(&*it);        // Insert builder above terminator

      if (isa<BranchInst>(terminator)) {
        BranchInst *branchInst = dyn_cast<BranchInst>(terminator);
        if (branchInst->isConditional()) {
          Value *newDest = Builder2.getInt32(idMap[&block]);

          Value *selectedDest = Builder2.CreateSelect(branchInst->getCondition(), Builder2.getInt32(idMap[branchInst->getSuccessor(0)]), Builder2.getInt32(idMap[branchInst->getSuccessor(1)]), "select");

          Value *newDiff = Builder2.CreateXor(newDest, selectedDest, "xorDiff");

          // Store the new Diff in diffMap
          if(diffMap.find(&block) == diffMap.end())
            diffMap[&block] = newDiff;

          // Store the destination block ID in destMap
          if(destMap.find(&block) == destMap.end())
            destMap[&block] = newDest;
        }
        else {
          Value *newDest = Builder2.getInt32(idMap[&block]);
          Value *newDiff = Builder2.CreateXor(newDest, Builder2.getInt32(idMap[branchInst->getSuccessor(0)]), "xorDiff");

          // Store the new Diff in diffMap
          if(diffMap.find(&block) == diffMap.end())
            diffMap[&block] = newDiff;

          // Store the destination block ID in destMap
          if(destMap.find(&block) == destMap.end())
            destMap[&block] = newDest;
        }
      } else if(terminator->getNumSuccessors() > 0) {
        Value *newDest = Builder2.getInt32(idMap[&block]);
        Value *newDiff = Builder2.CreateXor(Builder2.getInt32(idMap[&block]), Builder2.getInt32(idMap[terminator->getSuccessor(0)]), "xorDiff");

        // Store the new Diff in diffMap
        diffMap[&block] = newDiff;

        // Store the destination block ID in destMap
        destMap[&block] = newDest;
      }
    }
  }

  // Loop to fill the operands of the phi nodes
  for(auto bb=(*f).begin();bb!=(*f).end();bb++) {
    BasicBlock& block = *bb;    //get the basic block
    Instruction& first = *block.getFirstNonPHI();
    BasicBlock::iterator begin(first); 
    IRBuilder<> Builder3(&*begin); 

    //pull out the Phi nodes for this block
    PHINode *diffPhiNode = diffPhiMap[&block];
    PHINode *destPhiNode = destPhiMap[&block];

    // Find all of the predecessors for this Basic Block
    // Store them in a iterator_range
    iterator_range<pred_iterator> predRange = predecessors(&block);

    // Loop thru each predecessor in range
    for(BasicBlock *pred : predRange) {
      // If not null, add the incoming diff and dest value as an operand to the Phi
      if(diffMap[pred] != NULL) 
        diffPhiNode->addIncoming(diffMap[pred], pred);
      // If null, the predecessor's terminator was not a branch
      // So compute the Diff (pred's id ^ current id) and insert it into phi node
      else
        diffPhiNode->addIncoming((Builder3.getInt32(idMap[pred] ^ idMap[&block])), pred);
        
      if(destMap[pred] != NULL) 
        destPhiNode->addIncoming(destMap[pred], pred);
      // Compute dest which is current block's id
      else 
        destPhiNode->addIncoming(Builder3.getInt32(idMap[&block]), pred);
    }
  }
}

// Function to replicate all of the instructions in the function
// Excludes, Stores, Allocas, Calls, and Branches
// After replicating, it checks to see if it matches the original to catch any unexpected changes
void replicate(Function* f, Module *M) {
  int bbCount = 1;
  int iCount;
  std::unordered_map<Instruction*, Instruction*> cloneMap;
  //Loop through all of the basic blocks in each function
  for(auto bb=(*f).begin();bb!=(*f).end();bb++) {
    //BasicBlock& block = *bb;
    bbCount++;
    iCount = std::distance(bb->begin(),bb->end()); 
    int uniqueID = ((bbCount << 20) | (iCount << 8) |  ((bbCount*iCount) % 37));
    cloneMap = {};

    //Loop thru all of the instructions in each basic block
	  for(auto I = bb->begin(); I != bb->end(); I++) {
      Instruction& inst = *I;
      // Check if it's okay to clone instruction i
      //if (opcode != Instruction::Store && opcode != Instruction::Alloca && opcode != Instruction::Call && opcode != Instruction::Br) {
      if(canRep(inst)) {
        if(isUndefOrPoison(inst) == false) {
          // Clone instruction i
          Instruction *clone = I->clone();
          clone->insertBefore(&inst);   // Insert cloned instruction c into basic block beside i
          cloneMap[&inst] = clone;    // Map original instruction i to its clone
          
        }
      }
    }

    // Iterate over all cloned instructions
    for (auto& [i, c] : cloneMap) {
      for (int j = 0; j < c->getNumOperands(); j++) {
        // Change each operand to match the cloned version
        Value *op = c->getOperand(j);
        Instruction* operand = dyn_cast<Instruction>(op);

        // Check if operand is an instruction with a clone
        if (cloneMap.find(operand) != cloneMap.end()) {
          // Set operand to the cloned version
          c->setOperand(j, cloneMap[operand]);
        }
      }

      BasicBlock::iterator it;
      Value* cmpInst;
      Value* zextInst;

      if(isa<PHINode>(i)) {
        for(it = i->getParent()->begin(); isa<PHINode>(*it); it++);
      }
      else {
        BasicBlock::iterator notPhi(i); // get iterator for i
        notPhi++;
        it = notPhi;
      }

      IRBuilder<> Builder(&*it); // insert before it

      if(i->getType()->isIntegerTy() || i->getType()->isPointerTy()) { //int float or pointer in type class
        cmpInst = Builder.CreateICmpEQ(i, c, "icmpInst");// insert ICmpEQ after i and before it 
      } 
      else if(i->getType()->isFloatTy()) { //i->getType()->isFloatingPointTy()
        cmpInst = Builder.CreateFCmpOEQ(i, c, "fcmpInst");// insert FCmpEQ after i and before i
      }
      else {
        continue;
      }

      zextInst = Builder.CreateZExt(cmpInst, Type::getInt32Ty(getGlobalContext()), "zextInst"); //insert ZExt after ICmpEQ and before it

      std::vector<Value*> args;
      args.push_back(zextInst); // boolean
      args.push_back(Builder.getInt32(uniqueID)); // unique id
      Function *F = M->getFunction("assert_ft");
      Builder.CreateCall(F->getFunctionType(), F, args);    // Call Assert function
    }
    
  }
 }

// Function to see if the instrustion has poison or undefinedn operands
bool isUndefOrPoison(Instruction &I) {
  for (unsigned i = 0; i < I.getNumOperands(); ++i) {
    Value *Op = I.getOperand(i);
    if (isa<UndefValue>(Op) || isa<PoisonValue>(Op)) 
      return true;
  }
  return false;
}

// Function to see if the instruction is able to be replicated
bool canRep(Instruction &I) {
    int opcode = I.getOpcode();
    switch(opcode){
        case Instruction::Store:
        case Instruction::Call:
        case Instruction::Alloca: 	
        case Instruction::Br:
        {
          return false;
        }
        default: 
        {
          if(I.isTerminator())
            return false;
          else {
            SWFTAdded++;
            return true;
          }
        }
    }
}
