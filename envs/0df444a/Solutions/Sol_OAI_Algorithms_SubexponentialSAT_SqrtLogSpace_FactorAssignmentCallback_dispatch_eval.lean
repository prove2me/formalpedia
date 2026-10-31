-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.dispatch_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:03:33.264408+00:00
-- url     : https://prove2.me/submissions/91fea26e-8e34-464b-8e5d-2b9d674547c5

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram_dispatch_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dispatcher: reverse the incoming ID, classify it, and scan
only the selected source. No selected payload is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem program_runsIn (regs : Fin 8 → Bool) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ) (hvalid : hasMarked=true → m < clauses.length) :
    ∃ rf, rf 5=decide (f < rows.length) ∧ rf 6=(hasMarked && decide (f=rows.length)) ∧
      rf 7=hasMarked ∧
      RunsIn program (budget rows clauses m f)
        ((input regs rows clauses hasMarked m f).withPC (some program.entry))
        ((⟨rf,outputStacks rows clauses hasMarked m f⟩ : Data).withPC none) := by
  let d := input regs rows clauses hasMarked m f
  let a := afterTransfer d 2 6 0 1
  have hp : Eval prepare (3*f+6) d a := by
    dsimp [a]
    simpa [prepare,d,input,baseStacks,Nat.mul_add,Nat.add_assoc] using
      transfer_eval d 2 6 0 1 (by decide) (by decide)
  obtain ⟨n,e,hn,he,hs,h5,h6,h7⟩ := dispatch_eval a rows clauses hasMarked m f
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
    (by simp [a,d,afterTransfer,input,readRegs]) hvalid
    (by intro j hj; fin_cases j <;> simp_all [a,d,afterTransfer,
      StackRoutines.transferStacks,input,baseStacks])
    (by simp [TestClean,a,d,afterTransfer,StackRoutines.transferStacks,input,baseStacks])
  have hout : e.stacks=outputStacks rows clauses hasMarked m f := by
    rw [hs]
    funext j
    fin_cases j <;> simp [finishedStacks,a,d,afterTransfer,StackRoutines.transferStacks,
      input,baseStacks,outputStacks]
  have heq : e=(⟨e.regs,outputStacks rows clauses hasMarked m f⟩ : Data) := by
    exact state_ext rfl hout
  refine ⟨e.regs,h5,h6,?_,3*f+6+n+1,?_,?_⟩
  · simpa [a,d,afterTransfer,input,readRegs] using h7
  · unfold budget; omega
  · have ht := compiled_halt_trace (hp.seq he) 2 15
    rw [heq] at ht
    exact ht

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem register_injective : Function.Injective register := Fin.castAdd_injective 8 32
theorem stackMap_injective : Function.Injective stackMap := by decide

theorem stage_eval (a : Data) (hwork : a.stacks 359=[]) :
    Eval (.seq copyID readFlag) (7*(a.stacks 149).length+6) a (staged a) := by
  have hc := copy_eval a 149 152 359 0 1
    (by decide) (by decide) (by decide) (by decide) hwork
  have hp := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.peek (706 : Fin 768) (7 : Fin 40) 0) (copied a))
  have he : (StructuredProgram.Atom.peek (706 : Fin 768) (7 : Fin 40) 0).eval
      (copied a)=staged a := by
    simp [staged,copied,afterCopy,StackRoutines.copyStacks,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]
  rw [he] at hp
  convert hc.seq hp using 1
  all_goals try with_reducible_and_instances rfl

theorem command_eval (a : Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701=Encoding.encodeList id rows)
    (hclauses : a.stacks 700=Encoding.encodeList id clauses)
    (hcount : a.stacks 704=List.replicate rows.length true)
    (hmark : a.stacks 705=Encoding.encodeNat mark)
    (hflag : a.stacks 706=[marked])
    (hfactor : a.stacks 149=(Encoding.encodeNat factor).reverse)
    (hwork : ∀ i∈scratch, a.stacks i=[])
    (hvalid : marked=true → mark < clauses.length) :
    ∃ k rf, k ≤ 7*(a.stacks 149).length+6+
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval command k a (finished a rf rows clauses marked mark factor) ∧
      rf 5=decide (factor < rows.length) ∧
      rf 6=(marked && decide (factor=rows.length)) ∧ rf 7=marked := by
  obtain ⟨rf,h5,h6,h7,k,hk,he⟩ := LeafFactorDispatchProgram.program_runsIn
    ((staged a).regs ∘ register) rows clauses marked mark factor hvalid
  have hi : projectState register stackMap (staged a)=
      LeafFactorDispatchProgram.input ((staged a).regs ∘ register)
        rows clauses marked mark factor := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;>
        simp [staged,register,readRegs,hflag]
    · funext i
      fin_cases i <;>
        simp_all [stackMap,LeafFactorDispatchProgram.input,
          LeafFactorDispatchProgram.baseStacks,LeafFactorDispatchProgram.unary,
          staged,copied,afterCopy,StackRoutines.copyStacks,scratch]
  rw [← hi] at he
  have hd := eval_call_from_state LeafFactorDispatchProgram.program register stackMap
    (staged a) register_injective stackMap_injective he
  have hs := stage_eval a (hwork 359 (by simp [scratch]))
  exact ⟨_,rf,by omega,hs.seq hd,h5,h6,h7⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatchFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte-store frame for the paid factor dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem finished_role_hash (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) :
    (finished a rf rows clauses marked mark factor).regs 5 = rf 5 :=
  embedState_register register stackMap (staged a) _ register_injective 5

theorem finished_role_marked (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) :
    (finished a rf rows clauses marked mark factor).regs 6 = rf 6 :=
  embedState_register register stackMap (staged a) _ register_injective 6

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

theorem callbackInitial_low (a : Data) (i : Fin 768) :
    (callbackInitial a).stacks (lowStack i) =
      if i ∈ callbackScratch then [] else a.stacks (lowStack i) := by
  exact (embedState_stack localRegister lowStack a
    (clearManyState callbackScratch (projectState localRegister lowStack a))
    (Fin.castAdd_injective _ _) i).trans
    (clearMany_stacks callbackScratch (projectState localRegister lowStack a) i)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem dispatchInput_frame (a : FactorAssignmentProgram.Data) (i : Fin 768)
    (hi : i ∉ callbackScratch) :
    (dispatchInput a).stacks i = a.stacks (lowStack i) :=
  (callbackInitial_low a i).trans (ite_eq_right hi)

private theorem dispatchInput_work (a : FactorAssignmentProgram.Data) :
    ∀ i ∈ FactorDispatch.scratch, (dispatchInput a).stacks i = [] := by
  intro i hi
  have hmem : i ∈ callbackScratch := by
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hi))
  exact (callbackInitial_low a i).trans (ite_eq_left hmem)

/-- The native parser compares the complete original ID and returns both
role flags. Every copy, table scan and finite lifted return is charged. -/
theorem dispatch_eval_oai (a : FactorAssignmentProgram.Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hflag : a.stacks 706 = [marked])
    (hfactor : a.stacks 149 = (Encoding.encodeNat factor).reverse)
    (hvalid : marked = true → mark < clauses.length) :
    ∃ steps rf, steps ≤ 7 * (a.stacks 149).length + 7 +
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval (liftLow FactorDispatch.command 149 154) steps (callbackInitial a)
        (dispatched a rf rows clauses marked mark factor) ∧
      (dispatched a rf rows clauses marked mark factor).regs 5 =
        decide (factor < rows.length) ∧
      (dispatched a rf rows clauses marked mark factor).regs 6 =
        (marked && decide (factor = rows.length)) := by
  have hr : (dispatchInput a).stacks 701 = Encoding.encodeList id rows :=
    (dispatchInput_frame a 701 (by decide)).trans hrows
  have hc : (dispatchInput a).stacks 700 = Encoding.encodeList id clauses :=
    (dispatchInput_frame a 700 (by decide)).trans hclauses
  have hn : (dispatchInput a).stacks 704 = List.replicate rows.length true :=
    (dispatchInput_frame a 704 (by decide)).trans hcount
  have hm : (dispatchInput a).stacks 705 = Encoding.encodeNat mark :=
    (dispatchInput_frame a 705 (by decide)).trans hmark
  have hf : (dispatchInput a).stacks 706 = [marked] :=
    (dispatchInput_frame a 706 (by decide)).trans hflag
  have hid : (dispatchInput a).stacks 149 = (Encoding.encodeNat factor).reverse :=
    (dispatchInput_frame a 149 (by decide)).trans hfactor
  obtain ⟨k, rf, hk, he, h5, h6, _⟩ := FactorDispatch.command_eval
    (dispatchInput a) rows clauses marked mark factor hr hc hn hm hf hid
      (dispatchInput_work a) hvalid
  refine ⟨k + 1, rf, ?_, ?_, ?_, ?_⟩
  · have hl : (dispatchInput a).stacks 149 = a.stacks 149 :=
      dispatchInput_frame a 149 (by decide)
    rw [hl] at hk
    omega
  · exact eval_liftCommand_from_state FactorDispatch.command 149 154 id lowStack
      (callbackInitial a) Function.injective_id (Fin.castAdd_injective _ _) he
  · rw [show (dispatched a rf rows clauses marked mark factor).regs 5 =
        (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor).regs 5 from
      embedState_register id lowStack _ _ Function.injective_id 5]
    rw [FactorDispatch.finished_role_hash, h5]
  · rw [show (dispatched a rf rows clauses marked mark factor).regs 6 =
        (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor).regs 6 from
      embedState_register id lowStack _ _ Function.injective_id 6]
    rw [FactorDispatch.finished_role_marked, h6]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.dispatch_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.dispatch_eval_oai
