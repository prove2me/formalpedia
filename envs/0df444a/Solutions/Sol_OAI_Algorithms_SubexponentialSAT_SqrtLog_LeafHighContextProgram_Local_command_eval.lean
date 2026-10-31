-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:15:00.974437+00:00
-- url     : https://prove2.me/submissions/b68b54ee-1083-4cd9-bca0-10c349f59626

import Mathlib
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHighContextProgram_Local_flat_embed
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHighContextProgram_Local_mask_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHighContextProgram_Local_merge_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem copy_counter_eval (regs : Fin 4 → Bool) (counter mask forward : List Bool) :
    Eval copyCounter (7*counter.length+5)
      (state regs counter mask forward [] [] [] [] [] [] [])
      (state (readRegs regs 0 1 none) counter mask forward [] counter [] [] [] [] []) := by
  let a := state regs counter mask forward [] [] [] [] [] [] []
  have h := ListRegisterProgram.copy_run (0 : Fin 10) 4 8 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide) regs a.stacks rfl
  have hs : StackRoutines.copyStacks 0 4 a.stacks =
      (state (readRegs regs 0 1 none) counter mask forward [] counter [] [] [] [] []).stacks := by
    funext i; fin_cases i <;> simp [a,state,tapes,StackRoutines.copyStacks]
  have hlen : (a.stacks 0).length = counter.length := by simp [a, state, tapes]
  rw [hs, hlen] at h
  apply Eval.call
  exact h


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramFlatProject
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flat_project (regs : Fin 4 → Bool) (words : List (List Bool)) (mask forward : List Bool) : projectState flatRegs flatStacks (flatInitial regs words mask forward) =
    SubexponentialSAT.Subexp.AssignmentRecordViews.data (regs 0) (regs 1) (regs 2)
      (ProgramEncoding.encodeRecords words ++ []) [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · funext i; fin_cases i <;>
      simp [flatInitial,flatStacks,state,tapes]


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramFlatten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flatten_eval (regs : Fin 4 → Bool) (words : List (List Bool)) (mask forward : List Bool) :
    ∃ n rf, n ≤ 9*words.flatten.length+6*words.length+7 ∧ Eval flattenStep n
      (state regs (ProgramEncoding.encodeRecords words) mask forward []
        (ProgramEncoding.encodeRecords words) [] [] [] [] [])
      (state rf (ProgramEncoding.encodeRecords words) mask forward [] [] [] words.flatten [] [] []) := by
  let a := flatInitial regs words mask forward
  let count := 9*(words.map List.length).sum+6*words.length+7
  have raw := SubexponentialSAT.Subexp.AssignmentRecordViews.flatten_trace (regs 0) (regs 1) (regs 2) words [] []
  have hproject := flat_project regs words mask forward
  have ht := Eq.mp (congrArg (fun start : State 3 3 =>
    Trace SubexponentialSAT.Subexp.AssignmentRecordViews.flattenProgram count
      (start.withPC (some SubexponentialSAT.Subexp.AssignmentRecordViews.flattenProgram.entry))
      ((SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] []
        (words.flatten ++ [])).withPC none)) hproject.symm) raw
  have he := eval_call_from_state SubexponentialSAT.Subexp.AssignmentRecordViews.flattenProgram
    flatRegs flatStacks a (Fin.castAdd_injective 3 1) (by decide) ht
  let rout := flatOutRegs regs
  have hb := flat_embed regs words mask forward
  refine ⟨count,rout,?_,Eq.mp (congrArg (fun b : Data => Eval flattenStep count a b) hb) he⟩
  dsimp [count]
  rw [List.length_flatten]

end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramCopy
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem copy_mask_eval (regs : Fin 4 → Bool) (counter mask forward high : List Bool) :
    Eval copyMask (7*mask.length+5)
      (state regs counter mask forward [] [] [] high [] [] [])
      (state (readRegs regs 0 1 none) counter mask forward [] [] [] high mask [] []) := by
  let a := state regs counter mask forward [] [] [] high [] [] []
  have h := ListRegisterProgram.copy_run (1 : Fin 10) 7 8 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide) regs a.stacks rfl
  have hs : StackRoutines.copyStacks 1 7 a.stacks =
      (state (readRegs regs 0 1 none) counter mask forward [] [] [] high mask [] []).stacks := by
    funext i; fin_cases i <;> simp [a,state,tapes,StackRoutines.copyStacks]
  have hlen : (a.stacks (1 : Fin 10)).length = mask.length := by rfl
  apply Eval.call
  rw [hlen, hs] at h
  simpa only [a, state, StructuredProgram.State.withPC] using h


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem command_eval_oai (regs : Fin 4 → Bool) (words : List (List Bool)) (mask : List Bool)
    (hh : words.flatten.length = HighIncidenceProgram.Restriction.highCount mask) :
    ∃ n rf, n ≤ cost words mask ∧ Eval command n
      (state regs (ProgramEncoding.encodeRecords words) mask [] [] [] [] [] [] [] [])
      (state rf (ProgramEncoding.encodeRecords words) mask mask.reverse
        (HighIncidenceProgram.Restriction.zeroMerge mask words.flatten).reverse [] [] [] [] [] []) := by
  obtain ⟨nm,rm,hnm,hem⟩ := mask_eval regs (ProgramEncoding.encodeRecords words) mask
  have hec := copy_counter_eval rm (ProgramEncoding.encodeRecords words) mask mask.reverse
  obtain ⟨nf,rf,hnf,hef⟩ := flatten_eval (readRegs rm 0 1 none) words mask mask.reverse
  have hecm := copy_mask_eval rf (ProgramEncoding.encodeRecords words) mask mask.reverse words.flatten
  obtain ⟨nh,rh,hnh,heh⟩ := merge_eval (readRegs rf 0 1 none)
    (ProgramEncoding.encodeRecords words) mask mask.reverse words.flatten hh
  refine ⟨nm+(7*(ProgramEncoding.encodeRecords words).length+5+
    (nf+(7*mask.length+5+nh))),rh,?_,hem.seq (hec.seq (hef.seq (hecm.seq heh)))⟩
  unfold cost
  omega


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.command_eval_oai
