
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <map>
#include <utility>

using namespace llvm;
using namespace __gnu_cxx;

class Dynamic : public ModulePass {
	public:
		static char ID;
		Dynamic() : ModulePass(ID){}

		bool runOnModule(Module &M);
		void instrumentCode(Function &F);
		int doInstrumentBranches(Function &F, BasicBlock &B);
		void doInstrumentPrintf(Function &F, BasicBlock &B);
		void createFlagVar(Function &F, BasicBlock &B, BasicBlock::iterator i);

		std::map <std::string, int> varValue;
		int countVars,countForDepth, countFors;
		llvm::Value *branchString = NULL;
		Value *val1, *val2, *val3,*gi,*gii, *gj, *gjj, *gk, *gkk;
		BasicBlock *bb_for_end;
		AllocaInst * pa;//keep the local flag variable globally

		std::vector<BasicBlock *> outermostEnd;//contains end blocks of for loop to be instrumented
		int endEncountered = 0;//to count the number of for loops to instrument
		int current=0;
};


bool Dynamic::runOnModule(Module &M) 
{
	//get the global variables into value *
	val1 = M.getNamedGlobal("v1");
	val2 = M.getNamedGlobal("v2");
	val3 = M.getNamedGlobal("v3");
	gi = M.getNamedGlobal("i");
	gii = M.getNamedGlobal("ii");
	gj = M.getNamedGlobal("j");
	gjj = M.getNamedGlobal("jj");
	gk = M.getNamedGlobal("k");
	gkk = M.getNamedGlobal("kk");

	for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) 
	{
		if (!F->isDeclaration()) //for main() call the instrumentCode() function
		{
			instrumentCode(*F);
		}
	}
	
	return true;//because we are transforming the code
}

//counting the for levels, storing outermost for.end, instrumenting branches and printf calls
void Dynamic::instrumentCode(Function &F) 
{
	//finding the depth(levels) of for loops
	for(Function::iterator bb = F.begin(), e = F.end(); bb!=e; bb++)
	{
		std::string bbName = bb->getName();
		if(bbName.compare("for.cond")==0 || bbName.compare("for.cond3")==0 || bbName.compare("for.cond7")==0)
		{
			countForDepth ++;
		}
		if(bbName.compare("for.inc")==0)
		{
			break;
		}
	}

	//collecting the outermost for.end in a vector and also keep a count of them
	int EndCount =0;
	for(Function::iterator bb = F.begin(), e = F.end(); bb!=e; bb++)
	{
		if(bb->getName().contains("for.end"))
		{
			EndCount++;
			if(EndCount % countForDepth == 0)
			{
				bb_for_end = dyn_cast<BasicBlock>(bb);
				outermostEnd.push_back(bb_for_end);
				endEncountered++;
			}
		}
	}

	//instrument for entering the if-else statements inside the innermost for loop and jumping to outermost for.end stored in outermostEnd vector
	for(Function::iterator bb = F.begin(), e = F.end(); bb!=e; bb++)
	{
		//outs()<<bb->getName()<<"\n";
		for(BasicBlock::iterator i = bb->begin(),i2= bb->end(); i!=i2;i++)
		{
			if(i->getOpcode()== Instruction::Call)
			{
				if(CallInst *callInst = dyn_cast<CallInst>(&*i))
 				{

 					std::string funName = callInst->getCalledFunction()->getName();

 					//entering the flag variable in the main function and initializing to 0
 					if(callInst->getCalledFunction()->getName().contains("scanf"))
 					{
 						createFlagVar(F,*bb,i); //create a flag to track wheter the condition i==ii && j==jj && k==kk met
 					}


 					if(funName.compare("printf")==0)//if printf is called 
 					{
						Value * v = callInst->getArgOperand(0);
						GetElementPtrInst * vGEP = (GetElementPtrInst *)v;
						std::string arg = vGEP->getOperand(0)->getName();

						if(arg.compare(".str.1")==0)//if printf prints nothing
						{
							++i;
							++i;//jumping to last instr. in for.body

							for(int j=0; j<countForDepth; ++j)//taking to innermost for.body
							{
								++bb;
								++bb;
							}
								
							int noIfElse = doInstrumentBranches(F,*bb);//Instrumented if no If-else was detected else returned 0

							if(!noIfElse)// if If-else exists inside the for.body to be instrumented
							{
								std::string bbName = bb->getName();

								//outs()<<"Checking for end if..\n";
								while(bbName.compare(0,6,"if.end")!=0)
								{
									++bb;
									bbName = bb->getName();
								}
								//outs()<<"Found the end of if...\n";

								noIfElse = doInstrumentBranches(F,*bb);
							}

							//outs()<<"After instrumentation : "<<bb->getName()<<"\n";
							for(int j=0; j<countForDepth; ++j)
							{
								++bb;
								++bb;
							}
							//--bb;
							
						}
						
						
 					}


				}
			}
		}
	}

	//finding the for.end of outermost for loop, check if flag is 1 reset the flag and insert the printf calls inside for.end
	for(Function::iterator bb = F.begin(), e = F.end(); bb!=e; bb++)
	{
		for(int k=0; k<endEncountered; k++)
		{
			if(bb->getName().compare(outermostEnd[k]->getName())==0)
			{
				//outs()<<bb->getName()<<"\n";
				doInstrumentPrintf(F,*bb);
				break;
			}
		}
	}
	
}

//insert the store flag instruction in main beginning
void Dynamic::createFlagVar(Function &F, BasicBlock &B,BasicBlock::iterator i)
{
	CallInst * callInst = dyn_cast<CallInst>(i);
	Value* constantVal = ConstantInt::get(Type::getInt32Ty(F.getContext()), 0, false);
	IRBuilder<> builder(callInst);
	pa = new AllocaInst(llvm::Type::getInt32Ty(F.getContext()),0, constantVal,4,"flag",callInst);
	builder.CreateStore(constantVal,pa,false);
}

void Dynamic::doInstrumentPrintf(Function &F, BasicBlock &B)
{

	BasicBlock * currentBB = &B;
  	
  	Instruction * I = dyn_cast<Instruction>(currentBB->begin());

	IRBuilder<> builder(I);
	Value * x = builder.CreateLoad(pa);
	Value * y = ConstantInt::get(Type::getInt32Ty(F.getContext()), 1, false);
	Value* xEqualsY = builder.CreateICmpEQ(x, y, "tmp");

	TerminatorInst * tI = SplitBlockAndInsertIfThen(xEqualsY,I,false);

	builder.SetInsertPoint(tI);
	Value* flagVal = ConstantInt::get(Type::getInt32Ty(F.getContext()), 0, false); 
	builder.CreateStore(flagVal,pa,false);
	Value * v1 = builder.CreateLoad(val1);
	Value * v2 = builder.CreateLoad(val2);
	Value * v3 = builder.CreateLoad(val3);
	if (branchString == NULL)
		branchString = builder.CreateGlobalStringPtr("%d %d %d\n");
	std::vector<Value*> printfArgs;

	Module *M = builder.GetInsertBlock()->getModule();

	std::vector<Type *> printfParamTypes ;
	printfParamTypes.push_back(builder.getInt8PtrTy());
	printfParamTypes.push_back(builder.getInt32Ty());
	printfParamTypes.push_back(builder.getInt32Ty());
	printfParamTypes.push_back(builder.getInt32Ty());

	llvm::FunctionType *printfType = llvm::FunctionType::get(builder.getInt32Ty(), printfParamTypes, false);


	llvm::Constant *printfFunc = M->getOrInsertFunction("printf", printfType);

	printfArgs.push_back(branchString);
	printfArgs.push_back(v1);
	printfArgs.push_back(v2);
	printfArgs.push_back(v3);

	
	llvm::ArrayRef<llvm::Value*>  argsRef(printfArgs);
	builder.CreateCall(printfFunc, argsRef);

}

int Dynamic::doInstrumentBranches(Function &F, BasicBlock &B)
{	
	for(BasicBlock::iterator i = B.begin(),i2= B.end(); i!=i2;++i)
	{
		if(BranchInst * branchInst = dyn_cast<BranchInst>(&*i))
		{
			std::string label = i->getOperand(0)->getName();
			if(label.compare(0,7,"for.inc")==0)
			{

				if(countForDepth==1)
				{
					BasicBlock* cond_false = BasicBlock::Create(F.getContext(), "cond_false", B.getParent() , B.getNextNode());
	  				BasicBlock* cond_true = BasicBlock::Create(F.getContext(), "cond_true", B.getParent() , B.getNextNode());
	  


					IRBuilder<> builder(branchInst);
					Value * x = builder.CreateLoad(gi);
					Value * y = builder.CreateLoad(gii);
					Value* xEqualsY = builder.CreateICmpEQ(x, y, "tmp");
					builder.CreateCondBr(xEqualsY, cond_true, cond_false);

					--i;
					Instruction *CopyI = branchInst->clone();
					branchInst->dropAllReferences();
					branchInst->removeFromParent();

					builder.SetInsertPoint(cond_false);
					builder.Insert(CopyI);

					builder.SetInsertPoint(cond_true);
					Value* flagVal = ConstantInt::get(Type::getInt32Ty(F.getContext()), 1, false); 
					builder.CreateStore(flagVal,pa,false);
					builder.CreateBr(outermostEnd[current++]);
				}

				else if(countForDepth==2)
				{
					BasicBlock * nextNode = B.getNextNode();
					BasicBlock* cond_falsei = BasicBlock::Create(F.getContext(), "cond_falsei", B.getParent() , nextNode);
	  				BasicBlock* cond_truei = BasicBlock::Create(F.getContext(), "cond_truei", B.getParent() , nextNode);
	  				BasicBlock* cond_falsej = BasicBlock::Create(F.getContext(), "cond_falsej", B.getParent() , nextNode);
	  				BasicBlock* cond_truej = BasicBlock::Create(F.getContext(), "cond_truej", B.getParent() , nextNode);



					IRBuilder<> builder(branchInst);
					Value * xi = builder.CreateLoad(gi);
					Value * yi = builder.CreateLoad(gii);
					Value* xEqualsYi = builder.CreateICmpEQ(xi, yi, "tmp");
					builder.CreateCondBr(xEqualsYi, cond_truei, cond_falsei);

					--i;
					Instruction *CopyI = branchInst->clone();
					Instruction *CopyI2 = branchInst->clone();
					branchInst->dropAllReferences();
					branchInst->removeFromParent();


					builder.SetInsertPoint(cond_falsei);
					builder.Insert(CopyI);


					builder.SetInsertPoint(cond_truei);
					Value * xj = builder.CreateLoad(gj);
					Value * yj = builder.CreateLoad(gjj);
					Value* xEqualsYj = builder.CreateICmpEQ(xj, yj, "tmp2");
					builder.CreateCondBr(xEqualsYj, cond_truej, cond_falsej);


					builder.SetInsertPoint(cond_falsej);
					builder.Insert(CopyI2);

					builder.SetInsertPoint(cond_truej);
					Value* flagVal = ConstantInt::get(Type::getInt32Ty(F.getContext()), 1, false); 
					builder.CreateStore(flagVal,pa,false);
					builder.CreateBr(outermostEnd[current++]);

					//errs()<<F<<"\n";
				}

				else if(countForDepth==3)//take care of temp variable
				{
					BasicBlock * nextNode = B.getNextNode();
					BasicBlock* cond_falsei = BasicBlock::Create(F.getContext(), "cond_falsei", B.getParent() , nextNode);
	  				BasicBlock* cond_truei = BasicBlock::Create(F.getContext(), "cond_truei", B.getParent() , nextNode);
	  				BasicBlock* cond_falsej = BasicBlock::Create(F.getContext(), "cond_falsej", B.getParent() , nextNode);
	  				BasicBlock* cond_truej = BasicBlock::Create(F.getContext(), "cond_truej", B.getParent() , nextNode);
	  				BasicBlock* cond_falsek = BasicBlock::Create(F.getContext(), "cond_falsek", B.getParent() , nextNode);
	  				BasicBlock* cond_truek = BasicBlock::Create(F.getContext(), "cond_truek", B.getParent() , nextNode);
	  


					IRBuilder<> builder(branchInst);
					Value * xi = builder.CreateLoad(gi);
					Value * yi = builder.CreateLoad(gii);
					Value* xEqualsYi = builder.CreateICmpEQ(xi, yi, "tmp");
					builder.CreateCondBr(xEqualsYi, cond_truei, cond_falsei);

					--i;
					Instruction *CopyI = branchInst->clone();
					Instruction *CopyI2 = branchInst->clone();
					Instruction *CopyI3 = branchInst->clone();
					branchInst->dropAllReferences();
					branchInst->removeFromParent();


					builder.SetInsertPoint(cond_falsei);
					builder.Insert(CopyI);


					builder.SetInsertPoint(cond_truei);
					Value * xj = builder.CreateLoad(gj);
					Value * yj = builder.CreateLoad(gjj);
					Value* xEqualsYj = builder.CreateICmpEQ(xj, yj, "tmp2");
					builder.CreateCondBr(xEqualsYj, cond_truej, cond_falsej);

					builder.SetInsertPoint(cond_falsej);
					builder.Insert(CopyI2);


					builder.SetInsertPoint(cond_truej);
					Value * xk = builder.CreateLoad(gk);
					Value * yk = builder.CreateLoad(gkk);
					Value* xEqualsYk = builder.CreateICmpEQ(xk, yk, "tmp2");
					builder.CreateCondBr(xEqualsYk, cond_truek, cond_falsek);


					builder.SetInsertPoint(cond_falsek);
					builder.Insert(CopyI3);

					builder.SetInsertPoint(cond_truek);
					Value* flagVal = ConstantInt::get(Type::getInt32Ty(F.getContext()), 1, false); 
					builder.CreateStore(flagVal,pa,false);
					builder.CreateBr(outermostEnd[current++]);
				}
				

				//errs() << F << "\n" ;

				return 1;
			}
			else
			{
				//outs()<<"Reached Else...\n";
				if(++i==B.end())
				return 0;
			}
		}
		
	}




}
// Register the pass.
char Dynamic::ID = 0;
static RegisterPass<Dynamic> X("dynamic", "Dynamic Pass");


//where we have to take the input... during the program run or i/p to the llvm pass
//if given during program run then how to get the value input by user for ii,jj and kk.
//if given as i/p to llvm pass then should we compute v1,v2 and v3 in our llvm pass by knowing what operation to perform 

