-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_mismatch_branch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:45:54.976995+00:00
-- url     : https://prove2.me/submissions/730dc184-d195-43d3-824b-1a790e01795b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixInputTypes_program_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_UniversalRowMismatchTypes_filter_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

theorem extract_eval (i : Fin Δ) (u y : UniversalType r Q Δ) (a : Data)
    (ha : InputReady i u y a) :
    ∃ n ≤ extractBudget (r := r) (Q := Q) i, ∃ b : Data,
      Eval extract n a b ∧ b.stacks = extractedStacks a i u y := by
  let first := MatrixInputTypes.input i u y (a.regs ∘ inputRegs)
  let last := MatrixInputTypes.output i u y (a.regs ∘ inputRegs)
  obtain ⟨n, hn, ht⟩ := MatrixInputTypes.program_runsIn i u y (a.regs ∘ inputRegs)
  have hin : embedState inputRegs inputStacks a first = a := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 29 20)
    · intros; rfl
    · intros; rfl
    · intro j; exact ha j
    · intros; rfl
  let b := embedState inputRegs inputStacks a last
  have he : Eval extract n a b := by
    have h := eval_call_lifted MatrixInputProgram.program inputRegs inputStacks a
      (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 29 20) (a := first) (b := last) ht
    simpa only [extract, b, hin] using h
  refine ⟨n, hn, b, he, ?_⟩
  funext j
  by_cases hj : ∃ k, inputStacks k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [show b.stacks (inputStacks k) = last.stacks k from
      embedState_stack _ _ _ _ (Fin.castAdd_injective 29 20) k]
    have hk := ha k
    fin_cases k <;> first
      | rfl
      | simpa [last, extractedStacks, inputStacks, MatrixInputTypes.output,
          MatrixInputProgram.outputState, MatrixInputTypes.input, MatrixInputProgram.inputState]
          using hk.symm
  · rw [show b.stacks j = a.stacks j from embedState_stack_frame _ _ _ _ j hj]
    have h17 : j ≠ 17 := fun h => hj ⟨17, h.symm⟩
    have h18 : j ≠ 18 := fun h => hj ⟨18, h.symm⟩
    have h19 : j ≠ 19 := fun h => hj ⟨19, h.symm⟩
    have h20 : j ≠ 20 := fun h => hj ⟨20, h.symm⟩
    simp [extractedStacks, h17, h18, h19, h20]

theorem clearRows_eval (a : Data) :
    Eval clearRows
      (2 * (a.stacks 17).length + 3 + (2 * (a.stacks 18).length + 3 +
        (2 * (a.stacks 19).length + 3 + (2 * (a.stacks 20).length + 3))))
      a (cleared (cleared (cleared (cleared a 17) 18) 19) 20) := by
  have h17 := TupleProgram.clear_eval (17 : Fin 49) (0 : Fin 10) 1 a
  have h18 := TupleProgram.clear_eval (18 : Fin 49) (0 : Fin 10) 1 (cleared a 17)
  have h19 := TupleProgram.clear_eval (19 : Fin 49) (0 : Fin 10) 1 (cleared (cleared a 17) 18)
  have h20 := TupleProgram.clear_eval (20 : Fin 49) (0 : Fin 10) 1
    (cleared (cleared (cleared a 17) 18) 19)
  have h := h17.seq (h18.seq (h19.seq h20))
  simpa [clearRows, cleared, clearStacks] using h

theorem command_eval (i : Fin Δ) (u y : UniversalType r Q Δ) (a : Data)
    (ha : InputReady i u y a) (h45 : a.stacks 45 = []) :
    ∃ n ≤ extractBudget (r := r) (Q := Q) i + UniversalRowMismatchProgram.budget Q r + 8 * (Q * r) + 12,
      ∃ b : Data, Eval command n a b ∧
        b.stacks = Function.update a.stacks 45
          (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
            (MismatchPlanProgram.selectedPositions y.head (u.slot i)).reverse)) := by
  obtain ⟨ne, hne, b, hextract, hb⟩ := extract_eval i u y a ha
  have haLow (k : Fin 29) := ha k
  obtain ⟨nf, hnf, c, hfilter, hc⟩ := filter_eval y.head (u.slot i) b
    (by simp [hb, extractedStacks]) (by simp [hb, extractedStacks])
    (by simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
      MatrixInputProgram.inputState] using haLow 21)
    (by simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
      MatrixInputProgram.inputState] using haLow 22)
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 0
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 1
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 2
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 3
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 4
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 5
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 6
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 7
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 8
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 9
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 10
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 11
      · simpa [hb, extractedStacks] using h45)
  have hclear := clearRows_eval c
  let d := cleared (cleared (cleared (cleared c 17) 18) 19) 20
  refine ⟨_, ?_, d, hextract.seq (hfilter.seq hclear), ?_⟩
  · have hl17 : (c.stacks 17).length = Q * r := by
      simp [hc, hb, extractedStacks, ReadPlan.wordWidth]
    have hl18 : (c.stacks 18).length = Q * r := by
      simp [hc, hb, extractedStacks, ReadPlan.wordWidth]
    have hl19 : (c.stacks 19).length = Q * r := by
      simp [hc, hb, extractedStacks, ReadPlan.wordWidth]
    have hl20 : (c.stacks 20).length = Q * r := by
      simp [hc, hb, extractedStacks, ReadPlan.wordWidth]
    simp only [hl17, hl18, hl19, hl20]
    omega
  · funext k
    have h17 : a.stacks 17 = [] := by
      simpa [inputStacks, MatrixInputTypes.input, MatrixInputProgram.inputState] using haLow 17
    have h18 : a.stacks 18 = [] := by
      simpa [inputStacks, MatrixInputTypes.input, MatrixInputProgram.inputState] using haLow 18
    have h19 : a.stacks 19 = [] := by
      simpa [inputStacks, MatrixInputTypes.input, MatrixInputProgram.inputState] using haLow 19
    have h20 : a.stacks 20 = [] := by
      simpa [inputStacks, MatrixInputTypes.input, MatrixInputProgram.inputState] using haLow 20
    by_cases hk17 : k = 17
    · subst k; simp [d, cleared, clearStacks, hc, hb, extractedStacks, h17]
    by_cases hk18 : k = 18
    · subst k; simp [d, cleared, clearStacks, hc, hb, extractedStacks, h18]
    by_cases hk19 : k = 19
    · subst k; simp [d, cleared, clearStacks, hc, hb, extractedStacks, h19]
    by_cases hk20 : k = 20
    · subst k; simp [d, cleared, clearStacks, hc, hb, extractedStacks, h20]
    · simp [d, cleared, clearStacks, hc, hb, extractedStacks, hk17, hk18, hk19, hk20,
        Function.update_apply]

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured native stages used by the packed source dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem lowRegs_inj : Function.Injective lowRegs := Fin.castAdd_injective _ _
theorem mismatchPorts_inj : Function.Injective mismatchPorts := by decide

theorem mismatches_eval {r Q : ℕ} (u y : UniversalType r Q 1) (a : Data)
    (ha : UniversalRowMismatchTypes.InputReady (0 : Fin 1) u y
      (projectState lowRegs mismatchPorts a)) (he : a.stacks 71=[]) :
    ∃ n ≤ UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
      UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13,
      ∃ b : Data, Eval mismatches n a b ∧
        b.stacks=Function.update a.stacks 71
          (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
            (MismatchPlanProgram.selectedPositions y.head (u.slot 0)).reverse)) := by
  let small := projectState lowRegs mismatchPorts a
  obtain ⟨n,hn,z,hz,hzs⟩ := UniversalRowMismatchTypes.command_eval (0:Fin 1) u y small ha
    (by simpa [small,projectState,mismatchPorts] using he)
  let b := embedState lowRegs mismatchPorts a z
  have hh := eval_liftCommand_from_state UniversalRowMismatchTypes.command 23 45 lowRegs
    mismatchPorts a lowRegs_inj mismatchPorts_inj hz
  refine ⟨n+1,by omega,b,hh,?_⟩
  change Function.extend mismatchPorts z.stacks a.stacks=_
  rw [hzs,ProgramLinking.extend_update mismatchPorts_inj]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project lowRegs mismatchPorts a lowRegs_inj mismatchPorts_inj)
  change Function.extend mismatchPorts small.stacks a.stacks=a.stacks at hb
  rw [hb]
  rfl

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured staging and exact caller-store frames for the fixed source bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem stageTypes_stacks (a : Data) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) :
    (Staging.result 0 1 stageTypesOps a).stacks=
      Function.update (Function.update a.stacks 23 (a.stacks 289)) 24 (a.stacks 292) := by
  simp [stageTypesOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,h23,h24]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual scalar producer's numerator input already contains precisely
all low type-extractor inputs. No second pre-expanded input is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem numerator_mismatch_ready {r Q : ℕ} (a : Data) (c : Numerator.Saved)
    (start : Fin Q) (u y : UniversalType r Q 1) (bits : List Bool) (rf : Fin 16 → Bool)
    (hinput : ∀ i : Fin 64,
      (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks
        (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state c (fun _=>false) start u y [] [] ([],[])).stacks i) :
    UniversalRowMismatchTypes.InputReady (0:Fin 1) u y
      (projectState lowRegs mismatchPorts (vectorState a rf bits)) := by
  intro j
  have hh := hinput (j.castAdd 35)
  fin_cases j <;>
    simpa [projectState,vectorPorts,LayoutSourceValuesProgram.Native.numeratorPorts,
      vectorState,mismatchPorts,UniversalRowMismatchTypes.inputStacks,
      Numerator.state,Numerator.baseStacks,Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input,
      MatrixInputTypes.input,MatrixInputProgram.inputState] using hh

/-- Discharges the actual mismatch-trace premise of universal_cleanup_eval
from the same input invariant used by the native scalar-table program. -/
theorem native_mismatch_branch_oai {r Q : ℕ} (a : Data) (c : Numerator.Saved)
    (start : Fin Q) (u y : UniversalType r Q 1) (bits : List Bool) (rf : Fin 16 → Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) (h71 : a.stacks 71=[])
    (hinput : ∀ i : Fin 64,
      (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks
        (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state c (fun _=>false) start u y [] [] ([],[])).stacks i) :
    ∃ nm ≤ UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
        UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13,
      ∃ rm : Fin 16 → Bool, Eval mismatches nm (vectorState a rf bits)
        (branchState a rm bits (nativeIndices u y)) := by
  have hr := numerator_mismatch_ready a c start u y bits rf hinput
  have he : (vectorState a rf bits).stacks 71=[] := by
    simp [vectorState,stageTypes_stacks a h23 h24,h71]
  obtain ⟨nm,hnm,b,hb,hbs⟩ := mismatches_eval u y (vectorState a rf bits) hr he
  have heq : b=branchState a b.regs bits (nativeIndices u y) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simpa only [branchState,vectorState,nativeIndices,nativePositions] using hbs
  rw [heq] at hb
  exact ⟨nm,hnm,b.regs,hb⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_mismatch_branch_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_mismatch_branch_oai
