-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.descend_native_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:00:20.691903+00:00
-- url     : https://prove2.me/submissions/33e42117-7e9a-42b6-a2d1-f2f0af26c4b0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_load_run_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_result_headsize
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

open BitProgram

theorem readRegs_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (top : Option Bool) (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present top j = regs j := by
  simp [readRegs, hv, hp]

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

private theorem powerTwo_scan (word output : List Bool) (bit present flag : Bool) :
    Trace powerTwoProgram (4 * word.length + 2)
      (counterCfg 2 bit present flag word output)
      (counterCfg 6 false false flag [] (List.replicate word.length false ++ output)) := by
  induction word generalizing output bit present with
  | nil =>
      exact .cons (b := counterCfg 3 false false flag [] output)
        (by simp [step, powerTwoProgram, counterCfg, execInstr, readRegs])
        (.cons (by simp [step, powerTwoProgram, counterCfg, execInstr]) (.refl _))
  | cons b word ih =>
      have h := Computation.Trace.cons
        (show step powerTwoProgram (counterCfg 2 bit present flag (b :: word) output) =
          some (counterCfg 3 b true flag word output) by
            simp [step, powerTwoProgram, counterCfg, execInstr, readRegs])
        (Computation.Trace.cons
          (show step powerTwoProgram (counterCfg 3 b true flag word output) =
            some (counterCfg 4 b true flag word output) by
              simp [step, powerTwoProgram, counterCfg, execInstr])
          (Computation.Trace.cons
            (show step powerTwoProgram (counterCfg 4 b true flag word output) =
              some (counterCfg 5 false true flag word output) by
                simp [step, powerTwoProgram, counterCfg, execInstr])
            (Computation.Trace.cons
              (show step powerTwoProgram (counterCfg 5 false true flag word output) =
                some (counterCfg 2 false true flag word (false :: output)) by
                  simp [step, powerTwoProgram, counterCfg, execInstr])
              (ih (false :: output) false true))))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      simp [List.replicate_succ', List.append_assoc]

theorem powerTwo_trace (word : List Bool) (bit present flag : Bool) :
    Trace powerTwoProgram (4 * word.length + 5)
      ((localData bit present flag word []).withPC (some powerTwoProgram.entry))
      ((localData false false flag []
        (List.replicate word.length false ++ [true])).withPC none) := by
  have hstart : Trace powerTwoProgram 2 (counterCfg 0 bit present flag word [])
      (counterCfg 2 true present flag word [true]) :=
    .cons (b := counterCfg 1 true present flag word [])
      (by simp [step, powerTwoProgram, counterCfg, execInstr])
      (.cons (by simp [step, powerTwoProgram, counterCfg, execInstr]) (.refl _))
  have hend : Trace powerTwoProgram 1
      (counterCfg 6 false false flag [] (List.replicate word.length false ++ [true]))
      ((localData false false flag [] (List.replicate word.length false ++ [true])).withPC none) :=
    .cons (by simp [step, powerTwoProgram, counterCfg, execInstr, localData,
      StructuredProgram.State.withPC]) (.refl _)
  have h := (hstart.trans (powerTwo_scan word [true] true present flag)).trans hend
  have ht : 2 + (4 * word.length + 2) + 1 = 4 * word.length + 5 := by omega
  rw [ht] at h
  simpa [localData, StructuredProgram.State.withPC, counterCfg, powerTwoProgram] using h

theorem powerTwo_value (width : ℕ) :
    value (List.replicate width false ++ [true]) = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [List.replicate_succ, ih, pow_succ, Nat.mul_comm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem finish_empty {S : ℕ} (ports : List (Fin S)) (outputs : List (Fin S × Fin S))
    (a : Data S) (i : Fin S) (hi : i ∈ ports) :
    (finishState ports outputs a).stacks i = [] := by
  rw [finishState, resetMany_stacks, clearMany_stacks, ite_eq_left hi]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem prepare_frame {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (ht : i ≠ tmp) (hp : i ∉ ports) (hi : ∀ p ∈ inputs, i ≠ p.2) :
    (prepareState tmp ports inputs a).stacks i = a.stacks i := by
  unfold prepareState beforeCopies
  rw [copyMany_frame _ _ _ hi, resetMany_stacks, clearMany_stacks,
    ite_eq_right hp, clearMany_stacks]
  simp [ht]

theorem finish_frame {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hp : i ∉ ports) (ho : ∀ p ∈ outputs, i ≠ p.2) :
    (finishState ports outputs a).stacks i = a.stacks i := by
  have hmem : i ∉ outputs.map Prod.snd := by
    intro hi
    obtain ⟨p, hm, he⟩ := List.mem_map.mp hi
    exact ho p hm he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hp,
    copyMany_frame _ _ _ ho, clearMany_stacks, ite_eq_right hmem]

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem workPort_injective {s : ℕ} (hs : s ≤ 288) : Function.Injective (workPort hs) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [workPort] at this
  omega

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem work_mem_workPorts {s : ℕ} (hs : s ≤ 288) (j : Fin s) :
    workPort hs j ∈ workPorts hs := by
  simp only [workPorts,List.mem_ofFn]
  exact ⟨j,rfl⟩

theorem prepared_frame {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (i : Fin 768) (hi : Protected i) : (prepared hs ins a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ hi.2 (protected_not_workPorts hs hi)
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work hs hi q.2

theorem returned_word {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (ho : ∀ q ∈ outs,Protected q.2)
    (hd : (outs.map Prod.snd).Nodup) (p : Fin s × Fin 768) (hp : p ∈ outs) :
    (returned reg hs ins outs a b).stacks p.2=b.stacks p.1 := by
  have hd' : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hd
  have hsep : ∀ q ∈ outputCopies hs outs,∀ z ∈ outputCopies hs outs,q.1≠z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact (protected_ne_work hs (ho z' hz') q'.1).symm
  exact (finish_value (workPorts hs) (outputCopies hs outs) _ hd' hsep
    (workPort hs p.1,p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
    (protected_not_workPorts hs (ho p hp))).trans
      (embedState_stack reg (workPort hs) _ b (workPort_injective hs) p.1)

theorem returned_frame {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hi : Protected i)
    (hn : ∀ p ∈ outs,i≠p.2) : (returned reg hs ins outs a b).stacks i=a.stacks i := by
  have hno : ∀ p ∈ outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  exact (finish_frame _ _ _ _ (protected_not_workPorts hs hi) hno).trans
    ((embedState_stack_frame _ _ _ _ _ (by
      rintro ⟨j,hj⟩; exact protected_ne_work hs hi j hj.symm)).trans
      (prepared_frame hs ins a i hi))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem headResult_frame (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h650 : i≠650) (h651 : i≠651) :
    (headResult a n rows low W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) headInputs headOutputs a _ i hi
  intro p hp
  simp only [headOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl <;> assumption

theorem factorResult_frame (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h671 : i≠671) :
    (factorResult a A N rows W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) factorInputs factorOutputs a _ i hi
  intro p hp
  simp only [factorOutputs,List.mem_singleton] at hp
  subst p
  exact h671

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct the full ambient head-support mask from the IDs actually
selected. A low-variable mask alone is not a head-support mask. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem countResult_frame (a : Data) (i : Fin 768) (hi : Protected i) (h652 : i≠652) :
    (countResult a).stacks i=a.stacks i := by
  apply returned_frame countRegs (by decide) countInputs countOutputs a _ i hi
  intro p hp
  simp only [countOutputs,List.mem_singleton] at hp
  subst p
  exact h652

theorem scatterResult_frame (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ)
    (i : Fin 768) (hi : Protected i) (h670 : i≠670) :
    (scatterResult a regs n js).stacks i=a.stacks i := by
  apply returned_frame scatterRegs (by decide) scatterInputs scatterOutputs a _ i hi
  intro p hp
  simp only [scatterOutputs,List.mem_singleton] at hp
  subst p
  exact h670

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete head-selection stage. All three objects consumed by the
matrix/bucket phase are computed from runtime masters by fixed programs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem preparedHead_frame (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) (i : Fin 768)
    (hi : Protected i) (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
    (preparedHead a regs n N rows low W z).stacks i=a.stacks i := by
  rw [preparedHead,factorResult_frame _ _ _ _ _ _ _ hi h671,
    scatterResult_frame _ _ _ _ _ hi h670,countResult_frame _ _ hi h652]
  exact headResult_frame _ _ _ _ _ _ _ hi h650 h651

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The isolated bank never enlarges a non-output stack. This includes work
ports and the copy temporary, not only protected source masters. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem returned_nonoutput_eq {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hn : ∀ p∈outs,i≠p.2) :
    (returned reg hs ins outs a b).stacks i=
      if i∈workPorts hs ∨ i=temporary then [] else a.stacks i := by
  by_cases hw : i∈workPorts hs
  · rw [returned,finish_empty _ _ _ _ hw]
    simp [hw]
  have hno : ¬∃j,workPort hs j=i := by
    rintro ⟨j,rfl⟩
    exact hw (work_mem_workPorts hs j)
  have hin : ∀ p∈inputCopies hs ins,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    intro he
    exact hno ⟨q.2,he.symm⟩
  have hout : ∀ p∈outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  calc
    (returned reg hs ins outs a b).stacks i=(prepared hs ins a).stacks i :=
      (finish_frame _ _ _ i hw hout).trans
        (embedState_stack_frame reg (workPort hs) _ b i hno)
    _ = (beforeCopies temporary (workPorts hs) a).stacks i := copyMany_frame _ _ i hin
    _ = _ := by simp [beforeCopies,resetMany_stacks,clearMany_stacks,hw]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem shiftOutputs_protected : ∀ p∈shiftOutputs,Protected p.2 := by
  simp [shiftOutputs,Protected,temporary]

/-- Every persistent protected source except the head outputs and matrix
output668 is retained by the local loader. -/
theorem localResult_frame (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (hi : Protected i)
    (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h668 : i≠668)
    (h669 : i≠669) (h670 : i≠670) (h671 : i≠671) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks i=a.stacks i := by
  unfold localResult
  simp only [clearState,Function.update_of_ne h669]
  rw [returned_frame shiftRegs (by decide) shiftInputs shiftOutputs _ _ i hi
    (by simpa [shiftOutputs] using h668)]
  rw [returned_frame id (by decide) matrixInputs rawOutputs _ _ i hi
    (by simpa [rawOutputs] using h669)]
  exact preparedHead_frame a rp n N rows low W z i hi h650 h651 h652 h670 h671

theorem localResult_matrixWord (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks 668 =
      Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words) := by
  unfold localResult
  simp only [clearState, Function.update_of_ne (by decide : (668 : Fin 768) ≠ 669)]
  exact returned_word shiftRegs (by decide) shiftInputs shiftOutputs _ _
    shiftOutputs_protected (by decide) (15,668) (by simp [shiftOutputs])


/-- Every physical raw-matrix work tape is blank at the loader boundary. -/
theorem localResult_work_empty (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (j : Fin 288) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks (workPort (by decide) j)=[] := by
  have hne (q : Fin 768) (hq : 628 ≤ q.val) : workPort (by decide) j≠q := by
    intro h
    have hv := congrArg Fin.val h
    change 340+j.val=q.val at hv
    have := j.isLt
    omega
  unfold localResult
  simp only [clearState,Function.update_of_ne (hne 669 (by decide))]
  rw [returned_nonoutput_eq shiftRegs (by decide) shiftInputs shiftOutputs _ _ _
    (by simpa [shiftOutputs] using hne 668 (by decide))]
  split_ifs
  · rfl
  · rw [returned_nonoutput_eq id (by decide) matrixInputs rawOutputs _ _ _
      (by simpa [rawOutputs] using hne 669 (by decide))]
    simp only [Or.inl (work_mem_workPorts (by decide) j), ite_true, if_true]

theorem exportedState_matrix (a : State 16 896) (h847 : a.stacks 847=[]) :
    (exportedState a).stacks 847=a.stacks 668 := by
  simp [exportedState,clearMany_stacks,copyState,clearState,StackRoutines.copyStacks,h847]

theorem exportedState_raw (a : State 16 896) : (exportedState a).stacks 846=[] := by
  simp [exportedState,clearMany_stacks]

theorem exportedState_frame (a : State 16 896) (i : Fin 896)
    (hi : i≠659 ∧ i≠668 ∧ i≠669 ∧ i≠846 ∧ i≠847) :
    (exportedState a).stacks i=a.stacks i := by
  simp only [exportedState,clearMany_stacks,List.mem_cons,
    List.not_mem_nil,hi.2.1,hi.2.2.1,hi.2.2.2.1,or_self]
  rw [copyState_frame _ _ _ _ hi.2.2.2.2]
  simp [clearState,hi.1]

theorem addressStateFrom_frame (src : Fin 896) (a : State 16 896) (i : Fin 896)
    (hi : i∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks i=a.stacks i := by
  have h649 : i≠649 := by intro h; subst i; simp at hi
  rw [addressStateFrom,copyState_frame _ _ _ _ h649,clearMany_stacks]
  simp only [hi, ite_false]

theorem lowResultFrom_low (src : Fin 896) (a : State 16 896) (b : Data) (i : Fin 768)
    (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (exportedState (lowResultFrom src a b)).stacks (lowStacks i)=b.stacks i := by
  have hlow (j : Fin 768) (hj : i≠j) : lowStacks i≠lowStacks j :=
    fun h => hj (lowStacks.injective h)
  have hhigh (j : Fin 896) (hj : 768 ≤ j.val) : lowStacks i≠j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=j.val at hv
    have := i.isLt
    omega
  rw [exportedState_frame _ _ ⟨hlow 659 h659,hlow 668 h668,hlow 669 h669,
    hhigh 846 (by decide),hhigh 847 (by decide)⟩]
  exact embedState_stack id lowStacks _ b lowStacks.injective i


theorem lowResultFrom_frame (src : Fin 896) (a : State 16 896) (b : Data)
    (i : Fin 896) (hhigh : 768 ≤ i.val)
    (hi : i∉([846,847] : List (Fin 896))) :
    (exportedState (lowResultFrom src a b)).stacks i=a.stacks i := by
  have hn (j : Fin 896) (hj : j.val<768) : i≠j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h846 : i≠846 := by intro h; subst i; simp at hi
  have h847 : i≠847 := by intro h; subst i; simp at hi
  rw [exportedState_frame _ i ⟨hn 659 (by decide),hn 668 (by decide),
    hn 669 (by decide),h846,h847⟩]
  unfold lowResultFrom
  rw [embedState_stack_frame id lowStacks _ b i (by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega)]
  apply addressStateFrom_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨hn 649 (by decide),hn 659 (by decide),h846,h847⟩

theorem lowResultFrom_empty847 (src : Fin 896) (a : State 16 896) (b : Data) :
    (lowResultFrom src a b).stacks 847 = [] := by
  unfold lowResultFrom
  rw [embedState_stack_frame id lowStacks _ b 847 (by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 847 at hv
    have := j.isLt
    omega)]
  simp only [addressStateFrom, copyState_frame _ _ _ _
    (by decide : (847 : Fin 896) ≠ 649), clearMany_stacks,
    show (847 : Fin 896) ∈ [649,659,846,847] by decide, ite_true, if_true]

/-- The fixed16-register loader leaves every higher caller register intact. -/
theorem leafOutputFrom_registers (src : Fin 896) (frame : State 40 896) (b : Data)
    (i : Fin 40) (hi : 16 ≤ i.val) :
    (leafOutputFrom src frame b).regs i=frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  have := j.isLt
  omega


/-- The whole shifted matrix is returned on its dedicated physical tape. -/
theorem leafOutputFrom_matrix (src : Fin 896) (frame : State 40 896) (b : Data) :
    (leafOutputFrom src frame b).stacks 847=b.stacks 668 := by
  rw [show (leafOutputFrom src frame b).stacks 847=
    (exportedState (lowResultFrom src (projectState leafRegs id frame) b)).stacks 847 from
      embedState_stack leafRegs id frame _ Function.injective_id 847]
  rw [exportedState_matrix _ (lowResultFrom_empty847 src _ b)]
  exact embedState_stack id lowStacks _ b lowStacks.injective 668

theorem leafOutputFrom_raw_empty (src : Fin 896) (frame : State 40 896) (b : Data) :
    (leafOutputFrom src frame b).stacks 846=[] :=
  (embedState_stack leafRegs id frame _ Function.injective_id 846).trans (exportedState_raw _)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

private theorem pushFrame_cycle (bit v present : Bool) (word frames : List Bool) :
    Trace pushFrameProgram 5
      (ParserProgram.cfg (some 2) v present (bit :: word) frames)
      (ParserProgram.cfg (some 2) true true word (true :: bit :: frames)) := by
  refine .cons (b := ParserProgram.cfg (some 3) bit true word frames) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr, readRegs]
  refine .cons (b := ParserProgram.cfg (some 4) bit true word frames) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  refine .cons (b := ParserProgram.cfg (some 5) bit true word (bit :: frames)) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  refine .cons (b := ParserProgram.cfg (some 6) true true word (bit :: frames)) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  exact .cons (by simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]) (.refl _)

private theorem pushFrame_loop (word saved frames : List Bool) (v present : Bool) :
    Trace pushFrameProgram (5 * word.length + 3)
      (ParserProgram.cfg (some 2) v present word (Encoding.frame saved ++ frames))
      (ParserProgram.cfg none false false []
        (Encoding.frame (word.reverse ++ saved) ++ frames)) := by
  induction word generalizing saved v present with
  | nil =>
      refine .cons (b := ParserProgram.cfg (some 3) false false []
        (Encoding.frame saved ++ frames)) ?_ ?_
      · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr, readRegs]
      refine .cons (b := ParserProgram.cfg (some 7) false false []
        (Encoding.frame saved ++ frames)) ?_ ?_
      · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
      exact .cons (by simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]) (.refl _)
  | cons bit word ih =>
      have ht := (pushFrame_cycle bit v present word
        (Encoding.frame saved ++ frames)).trans (ih (bit :: saved) true true)
      have htime : 5 + (5 * word.length + 3) = 5 * (word.length + 1) + 3 := by omega
      simpa only [List.length_cons, htime, Encoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append,
        List.nil_append] using ht

/-- Exact fixed-table suspension, including initialization and halt. -/
theorem pushFrame_trace (word frames : List Bool) (v present : Bool) :
    Trace pushFrameProgram (5 * word.length + 5)
      (ParserProgram.cfg (some 0) v present word frames)
      (ParserProgram.cfg none false false [] (Encoding.frame word.reverse ++ frames)) := by
  have ht := pushFrame_loop word [] frames false present
  have ht' : Trace pushFrameProgram (5 * word.length + 3 + 1 + 1)
      (ParserProgram.cfg (some 0) v present word frames)
      (ParserProgram.cfg none false false [] (Encoding.frame word.reverse ++ frames)) := by
    refine .cons (b := ParserProgram.cfg (some 1) false present word frames) ?_ ?_
    · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
    refine .cons (b := ParserProgram.cfg (some 2) false present word (false :: frames)) ?_ ?_
    · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
    simpa [Encoding.frame] using ht
  simpa only [Nat.add_assoc] using ht'

theorem suspendedFrames_length_le (frames : List (List Bool)) (width levels : ℕ)
    (hdepth : frames.length ≤ levels)
    (hwidth : ∀ frame ∈ frames, frame.length ≤ width) :
    (suspendedFrames frames).length ≤ (2 * width + 1) * levels := by
  have h : (suspendedFrames frames).length ≤ (2 * width + 1) * frames.length := by
    induction frames with
    | nil => simp [suspendedFrames]
    | cons frame frames ih =>
        have hf := hwidth frame (by simp)
        have hh := ih (by simp only [List.length_cons] at hdepth; omega)
          (fun word hw => hwidth word (by simp [hw]))
        simp only [suspendedFrames, List.flatMap_cons, List.length_append,
          Encoding.length_frame, List.length_reverse, List.length_cons,
          Nat.mul_add, Nat.mul_one] at *
        omega
  exact h.trans (Nat.mul_le_mul_left _ hdepth)

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

theorem initialFuel_eval (a : State 40 896)
    (he : a.stacks initialFuelPorts.scratch = []) :
    Eval initialFuelCommand (4 * (a.stacks initialFuelPorts.counter).length + 5) a
      (initialFuelState a) := by
  have ht := eval_call_lifted Counters.powerTwoProgram initialFuelPorts.register
    (CounterForPrograms.stackPorts initialFuelPorts) a initialFuelPorts.register.injective
    (CounterForPrograms.stackPorts initialFuelPorts).injective
    (Counters.powerTwo_trace (a.stacks initialFuelPorts.counter)
      (a.regs (initialFuelPorts.register 0)) (a.regs (initialFuelPorts.register 1))
      (a.regs (initialFuelPorts.register 2)))
  change Eval initialFuelCommand _
    (CounterForPrograms.install initialFuelPorts a _ _ _ _ []) (initialFuelState a) at ht
  rw [← he, CounterForPrograms.install_self] at ht
  exact ht

theorem reset_eval (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (he : a.stacks (tupleStacks 7) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hp : a.stacks (tupleStacks 4) = []) :
    Eval resetCommand (18 * h + 17) a (resetState a) := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  have hb := copyWord_eval 651 (tupleStacks 2) (tupleStacks 5)
    (by decide) (by decide) (by decide) a ht
  have hbt : b.stacks (tupleStacks 5) = [] := by
    simpa [b, copyState, StackRoutines.copyStacks] using ht
  have hc := copyWord_eval 651 (tupleStacks 4) (tupleStacks 5)
    (by decide) (by decide) (by decide) b hbt
  have hce : c.stacks initialFuelPorts.scratch = [] := by
    simpa [c, b, copyState, StackRoutines.copyStacks, initialFuelPorts] using he
  have hi := initialFuel_eval c hce
  have hall := Eval.seq hb (Eval.seq hc (Eval.seq hi
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom
      (.set controllerPorts.available true) _))
      (Eval.base (StructuredProgram.Eval.atom (.set controllerPorts.fresh false) _)))))
  have hbword : b.stacks 651 = List.replicate h false := by
    have hne : (651 : Fin 896) ≠ tupleStacks 2 := by decide
    simpa [b, copyState, StackRoutines.copyStacks, hne] using hw
  have hcpayload : c.stacks initialFuelPorts.counter =
      List.replicate h false := by
    change b.stacks 651 ++ b.stacks (tupleStacks 4) = _
    rw [hbword]
    have hbpayload : b.stacks (tupleStacks 4) = [] := by
      simpa [b, copyState, StackRoutines.copyStacks] using hp
    simp only [hbpayload, List.append_nil]
  change Eval resetCommand _ a (resetState a) at hall
  convert hall using 1
  all_goals try with_reducible_and_instances rfl
  simp only [hw, hbword, hcpayload, List.length_replicate]
  omega

/-- Empty heads are initialized with the sole empty assignment and fuel one. -/
theorem resetState_words (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = []) :
    (resetState a).stacks (tupleStacks 2) = List.replicate h false ∧
      (resetState a).stacks (tupleStacks 7) = List.replicate h false ++ [true] ∧
      (resetState a).stacks (tupleStacks 4) = [] := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  have hbsource : b.stacks 651 = List.replicate h false := by
    have hne : (651 : Fin 896) ≠ tupleStacks 2 := by decide
    simpa [b, copyState, StackRoutines.copyStacks, hne] using hw
  have hcpayload : c.stacks (tupleStacks 4) = List.replicate h false := by
    change b.stacks 651 ++ b.stacks (tupleStacks 4) = _
    rw [hbsource]
    have hp' : b.stacks (tupleStacks 4) = [] := by
      simpa [b, copyState, StackRoutines.copyStacks] using hp
    simp only [hp', List.append_nil]
  have hccandidate : c.stacks (tupleStacks 2) = List.replicate h false := by
    simp [c, b, copyState, StackRoutines.copyStacks, hc, hw]
  constructor
  · change (initialFuelState c).stacks (tupleStacks 2) = _
    unfold initialFuelState
    rw [CounterForPrograms.install_other_stack initialFuelPorts c _ _ _ _ _
      (tupleStacks 2) (by decide) (by decide)]
    exact hccandidate
  constructor
  · change (CounterForPrograms.install initialFuelPorts c _ _ _ _ _).stacks
      initialFuelPorts.scratch = _
    rw [CounterForPrograms.install_scratch]
    change List.replicate (c.stacks (tupleStacks 4)).length false ++ [true] = _
    simp only [hcpayload, List.length_replicate]
  · exact CounterForPrograms.install_counter initialFuelPorts c _ _ _ _ _

private theorem extend_restrict_eq {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ he => congrArg g he) g a
  · exact Function.extend_apply' _ _ _ h

private theorem word_embed_self (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) :
    embedState frameRegisters (wordPorts src dst h) a
      (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)) = a := by
  apply CounterForPrograms.data_ext
  · have hr : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).regs =
        a.regs ∘ frameRegisters := by
      first | done | (funext i; fin_cases i <;> rfl)
    change Function.extend frameRegisters _ a.regs = a.regs
    rw [hr, extend_restrict_eq]
  · have hs : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).stacks =
        a.stacks ∘ wordPorts src dst h := by
      first | done | (funext i; fin_cases i <;> rfl)
    change Function.extend (wordPorts src dst h) _ a.stacks = a.stacks
    rw [hs, extend_restrict_eq]

theorem pushWord_eval (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    Eval (pushWordCommand src dst h) (5 * (a.stacks src).length + 5) a
      (pushWordState src dst h a) := by
  have ht := eval_call_lifted pushFrameProgram frameRegisters (wordPorts src dst h) a
    frameRegisters.injective (wordPorts src dst h).injective
    (a := frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst))
    (b := frameState false false [] (Encoding.frame (a.stacks src).reverse ++ a.stacks dst))
    (pushFrame_trace (a.stacks src) (a.stacks dst) (a.regs 0) (a.regs 1))
  rw [word_embed_self] at ht
  exact ht

theorem pushWordState_src (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    (pushWordState src dst h a).stacks src = [] :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 0

theorem pushWordState_dst (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    (pushWordState src dst h a).stacks dst =
      Encoding.frame (a.stacks src).reverse ++ a.stacks dst :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 1

theorem pushWordState_outside (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (pushWordState src dst h a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

theorem saveCursor_eval (a : State 40 896) :
    Eval saveCursorCommand
      (5 * (a.stacks (tupleStacks 2)).length + 5 * (a.stacks (tupleStacks 7)).length + 10)
      a (saveCursorState a) := by
  have ht := Eval.seq (pushWord_eval (tupleStacks 2) (tupleStacks 0) (by decide) a)
    (pushWord_eval (tupleStacks 7) (tupleStacks 0) (by decide) _)
  have hw := pushWordState_outside (tupleStacks 2) (tupleStacks 0) (by decide) a
    (tupleStacks 7) (by decide) (by decide)
  change Eval saveCursorCommand _ a (saveCursorState a) at ht
  rw [hw] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem saveCursorState_words (a : State 40 896) :
    (saveCursorState a).stacks (tupleStacks 2) = [] ∧
      (saveCursorState a).stacks (tupleStacks 7) = [] ∧
      (saveCursorState a).stacks (tupleStacks 0) =
        Encoding.frame (a.stacks (tupleStacks 7)).reverse ++
          Encoding.frame (a.stacks (tupleStacks 2)).reverse ++ a.stacks (tupleStacks 0) := by
  constructor
  · unfold saveCursorState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide), pushWordState_src]
  constructor
  · exact pushWordState_src _ _ _ _
  · unfold saveCursorState
    rw [pushWordState_dst, pushWordState_dst,
      pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    exact List.append_assoc _ _ _ |>.symm

theorem recordRepresentative_eval (a : State 40 896)
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = []) :
    Eval recordRepresentativeCommand (12 * (a.stacks (tupleStacks 2)).length + 10) a
      (recordRepresentativeState a) := by
  have hc := copyWord_eval (tupleStacks 2) (tupleStacks 4) (tupleStacks 5)
    (by decide) (by decide) (by decide) a ht
  have hh := Eval.seq hc (pushWord_eval (tupleStacks 4) (tupleStacks 1) (by decide) _)
  have hw : (copyState (tupleStacks 2) (tupleStacks 4) a).stacks (tupleStacks 4) =
      a.stacks (tupleStacks 2) := by simp [copyState, hp]
  change Eval recordRepresentativeCommand _ a (recordRepresentativeState a) at hh
  rw [hw] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem recordRepresentativeState_words (a : State 40 896)
    (hp : a.stacks (tupleStacks 4) = []) :
    (recordRepresentativeState a).stacks (tupleStacks 1) =
        Encoding.frame (a.stacks (tupleStacks 2)).reverse ++ a.stacks (tupleStacks 1) ∧
      (recordRepresentativeState a).stacks (tupleStacks 2) = a.stacks (tupleStacks 2) ∧
      (recordRepresentativeState a).stacks (tupleStacks 4) = [] := by
  constructor
  · unfold recordRepresentativeState
    rw [pushWordState_dst]
    simp [copyState, StackRoutines.copyStacks, hp]
  constructor
  · unfold recordRepresentativeState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    simp [copyState, StackRoutines.copyStacks]
  · exact pushWordState_src _ _ _ _

theorem descendLevel_eval (a : State 40 896) :
    Eval descendLevelCommand 5 a (descendLevelState a) :=
  .base (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))))

theorem descendLevelState_words (a : State 40 896) (remaining address : ℕ)
    (hr : a.stacks (tupleStacks 6) = List.replicate (remaining + 1) true)
    (ha : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendLevelState a).stacks (tupleStacks 6) = List.replicate remaining true ∧
      (descendLevelState a).stacks (tupleStacks 9) = List.replicate (address + 1) true ∧
      (descendLevelState a).regs controllerPorts.leaf = decide (remaining = 0) := by
  have h69 : tupleStacks 6 ≠ tupleStacks 9 := by decide
  cases remaining <;>
    simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hr, ha, List.replicate_succ, controllerPorts, h69, Ne.symm h69]

theorem clearWord_eval (src : Fin 896) (a : State 40 896) :
    Eval (clearWord src) (2 * (a.stacks src).length + 3) a (clearState src a) := by
  have ht := StackRoutines.clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  exact .call _ (by simpa [clearState, StackRoutines.clearResult, StackRoutines.clearStacks,
    StructuredProgram.State.withPC, StackRoutines.clearProgram, Nat.add_assoc] using hh)

theorem clearWords_eval (ports : List (Fin 896)) (a : State 40 896) :
    Eval (clearWords ports) (clearWordsTime ports a) a (clearWordsState ports a) := by
  induction ports generalizing a with
  | nil => exact .base (.skip _)
  | cons src rest ih => exact .seq (clearWord_eval src a) (ih _)

theorem clearWordsState_stacks (ports : List (Fin 896)) (a : State 40 896)
    (i : Fin 896) :
    (clearWordsState ports a).stacks i = if i ∈ ports then [] else a.stacks i := by
  induction ports generalizing a with
  | nil => simp [clearWordsState]
  | cons src rest ih =>
    rw [clearWordsState, ih]
    by_cases hr : i ∈ rest
    · simp [hr]
    · by_cases hi : i = src
      · subst i
        simp [hr, clearState]
      · simp [hr, hi, clearState]

theorem resetState_assignment (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = []) :
    (resetState a).stacks (tupleStacks 2) = ExecCNFTupleEnumeration.fixedBits h 0 := by
  rw [(resetState_words a h hw hc hp).1]
  exact ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
    (by simp [ExecCNFTupleEnumeration.fixedBits_value h 0 (Nat.pow_pos (by decide))])

theorem resetState_source (a : State 40 896) :
    (resetState a).stacks 651 = a.stacks 651 := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  change (initialFuelState c).stacks 651 = a.stacks 651
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts c _ _ _ _ _ 651
    (by decide) (by decide)]
  simp [c, b, copyState, StackRoutines.copyStacks,
    (by decide : (651 : Fin 896) ≠ tupleStacks 2),
    (by decide : (651 : Fin 896) ≠ tupleStacks 4)]

theorem resetState_scratch (a : State 40 896) :
    (resetState a).stacks (tupleStacks 5) = a.stacks (tupleStacks 5) := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  change (initialFuelState c).stacks (tupleStacks 5) = a.stacks (tupleStacks 5)
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts c _ _ _ _ _
    (tupleStacks 5) (by decide) (by decide)]
  simp [c, b, copyState, StackRoutines.copyStacks]

theorem resetGenerator_eval (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (he : a.stacks (tupleStacks 7) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hp : a.stacks (tupleStacks 4) = []) :
    Eval resetGeneratorCommand (25 * h + 22) a (resetGeneratorState a) := by
  have hr := reset_eval a h hw he ht hp
  have hh := copyWord_eval 651 (tupleStacks 8) (tupleStacks 5)
    (by decide) (by decide) (by decide) (resetState a) ((resetState_scratch a).trans ht)
  have hall := Eval.seq hr hh
  rw [resetState_source, hw, List.length_replicate] at hall
  change Eval resetGeneratorCommand _ a (resetGeneratorState a) at hall
  convert hall using 1
  all_goals try with_reducible_and_instances rfl
  omega

/-- Generic frame operations preserve every controller flag. -/
theorem pushWordState_register_frame (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (pushWordState src dst h a).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact h0 hj.symm
  · exact h1 hj.symm

theorem clearWordsState_register_frame (ports : List (Fin 896))
    (a : State 40 896) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (clearWordsState ports a).regs i = a.regs i := by
  induction ports generalizing a with
  | nil => rfl
  | cons src rest ih =>
    rw [clearWordsState, ih]
    exact StackRoutines.readRegs_frame a.regs 0 1 i none h0 h1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

section Frames

open ExecCNFTupleEnumeration SignatureTupleProgram

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem representativeWords_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    representativeWords h key (depth + 1) (Fin.snoc ancestors rep) =
      representativeWords h key depth ancestors ++ [fixedBits (h depth) rep.val.val] := by
  simp only [representativeWords, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append]
  rfl

theorem representativeFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    representativeFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      Encoding.frame (fixedBits (h depth) rep.val.val).reverse ++
        representativeFrames h key depth ancestors := by
  simp [representativeFrames, representativeWords_snoc, suspendedFrames, List.reverse_append]

theorem cursorFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      cursorFrame (h depth) rep.val.val ++ cursorFrames h key depth ancestors := by
  simp only [cursorFrames, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatten_cons]
  rfl

theorem representativeFrames_length_le (depth hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hh : ∀ d < depth, h d ≤ hmax) :
    (representativeFrames h key depth ancestors).length ≤ (2 * hmax + 1) * depth := by
  apply suspendedFrames_length_le _ hmax depth
  · simp [representativeWords]
  · intro word hw
    rw [List.mem_reverse, representativeWords, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    simpa using hh i.val i.isLt

private theorem flatten_length_le (words : List (List Bool)) (bound : ℕ)
    (hw : ∀ word ∈ words, word.length ≤ bound) : words.flatten.length ≤ words.length * bound := by
  induction words with
  | nil => simp
  | cons word words ih =>
      have hword := hw word (by simp)
      have htail := ih (fun w hmem => hw w (by simp [hmem]))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem cursorFrame_length (width candidate : ℕ) :
    (cursorFrame width candidate).length = 4 * width + 4 := by
  simp [cursorFrame]
  omega

theorem cursorFrames_length_le (depth hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hh : ∀ d < depth, h d ≤ hmax) :
    (cursorFrames h key depth ancestors).length ≤ (4 * hmax + 4) * depth := by
  unfold cursorFrames
  have hb := flatten_length_le
    (List.ofFn fun i : Fin depth => cursorFrame (h i.val) (ancestors i).val.val).reverse
    (4 * hmax + 4) (by
      intro word hw
      rw [List.mem_reverse, List.mem_ofFn] at hw
      obtain ⟨i, rfl⟩ := hw
      rw [cursorFrame_length]
      have hi := hh i.val i.isLt
      omega)
  simpa only [List.length_reverse, List.length_ofFn, Nat.mul_comm] using hb

/-- Both persistent frame banks together use polynomially many actual bits,
including framing delimiters for empty heads. -/
theorem retainedFrames_length_le (depth levels hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hd : depth ≤ levels)
    (hh : ∀ d < depth, h d ≤ hmax) :
    (representativeFrames h key depth ancestors).length +
      (cursorFrames h key depth ancestors).length ≤ 6 * levels * (hmax + 1) := by
  have hr := representativeFrames_length_le h key depth hmax ancestors hh
  have hc := cursorFrames_length_le h key depth hmax ancestors hh
  have hm := Nat.mul_le_mul_right (6 * (hmax + 1)) hd
  nlinarith

end Frames

section NativeFrames

open ExecCNFTupleEnumeration SignatureTupleProgram StructuredCalls

private theorem record_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

private theorem save_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hf : i ≠ tupleStacks 0) (hc : i ≠ tupleStacks 2) (hr : i ≠ tupleStacks 7) :
    (saveCursorState a).stacks i = a.stacks i := by
  unfold saveCursorState
  rw [pushWordState_outside _ _ _ _ _ hr hf, pushWordState_outside _ _ _ _ _ hc hf]

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- The actual record-then-save commands install precisely the dependent
child prefix in both persistent banks and empty their consumed words. -/
theorem retainFrames_state (depth : ℕ) (ancestors : Prefix (Representatives key) depth)
    (rep : Representatives key depth) (a : StructuredProgram.State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key depth ancestors)
    (hr : a.stacks (tupleStacks 1) = representativeFrames h key depth ancestors)
    (hc : a.stacks (tupleStacks 2) = fixedBits (h depth) rep.val.val)
    (hn : a.stacks (tupleStacks 7) = fixedBits (h depth + 1) (2 ^ h depth - rep.val.val))
    (hp : a.stacks (tupleStacks 4) = []) :
    let b := saveCursorState (recordRepresentativeState a)
    b.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) ∧
    b.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) (Fin.snoc ancestors rep) ∧
    b.stacks (tupleStacks 2) = [] ∧ b.stacks (tupleStacks 7) = [] ∧
    b.stacks (tupleStacks 4) = [] := by
  dsimp only
  have hs := saveCursorState_words (recordRepresentativeState a)
  have hrec := recordRepresentativeState_words a hp
  refine ⟨?_, ?_, hs.1, hs.2.1, ?_⟩
  · rw [hs.2.2, hrec.2.1, record_outside a (tupleStacks 7) (by decide) (by decide),
      record_outside a (tupleStacks 0) (by decide) (by decide), hc, hn, hf,
      cursorFrames_snoc, cursorFrame]
  · rw [save_outside _ (tupleStacks 1) (by decide) (by decide) (by decide),
      hrec.1, hc, hr, representativeFrames_snoc]
  · rw [save_outside _ (tupleStacks 4) (by decide) (by decide) (by decide), hrec.2.2]

theorem retainFrames_eval (width candidate : ℕ) (a : StructuredProgram.State 40 896)
    (hc : a.stacks (tupleStacks 2) = fixedBits width candidate)
    (hn : a.stacks (tupleStacks 7) = fixedBits (width + 1) (2 ^ width - candidate))
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = []) :
    Eval (.seq recordRepresentativeCommand saveCursorCommand) (22 * width + 25) a
      (saveCursorState (recordRepresentativeState a)) := by
  have he := (recordRepresentative_eval a hp ht).seq
    (saveCursor_eval (recordRepresentativeState a))
  rw [(recordRepresentativeState_words a hp).2.1,
    record_outside a (tupleStacks 7) (by decide) (by decide), hc, hn] at he
  simp only [fixedBits_length] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  omega

end NativeFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open BitProgram StructuredCalls SignatureTupleProgram

theorem initial_remaining_word (h : ℕ) :
    List.replicate h false ++ [true] =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h) := by
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have hb : 2 ^ h < 2 ^ (h + 1) := by rw [pow_succ]; omega
  exact ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
    (by rw [Counters.powerTwo_value, ExecCNFTupleEnumeration.fixedBits_value _ _ hb])


section CursorStorage

open SignatureTupleDFS SignatureTupleTraversal

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem AncestorStorage.frame_bound {levels base depth : ℕ}
    {ancestors : Prefix (Representatives key) depth} {a : State 40 896}
    (ha : AncestorStorage h key levels base depth ancestors a) (hmax : ℕ)
    (hh : ∀ d < levels, h d ≤ hmax) :
    (a.stacks (tupleStacks 0)).length + (a.stacks (tupleStacks 1)).length ≤
      6 * levels * (hmax + 1) := by
  rw [ha.cursors, ha.representatives, Nat.add_comm]
  exact retainedFrames_length_le h key depth levels hmax ancestors ha.depth_le
    (fun d hd => hh d (hd.trans_le ha.depth_le))


end CursorStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual state refinements for the fixed attained-signature controller.
Each lemma follows concrete commands already installed in the native ABI. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal

theorem recordRepresentative_outside (a : State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

theorem retainedState_outside (a : State 40 896) (i : Fin 896)
    (h0 : i ≠ tupleStacks 0) (h1 : i ≠ tupleStacks 1)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (retainedState a).stacks i = a.stacks i := by
  unfold retainedState saveCursorState
  rw [pushWordState_outside _ _ _ _ _ h7 h0,
    pushWordState_outside _ _ _ _ _ h2 h0, recordRepresentative_outside a i h1 h4]

theorem retainedState_register (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) : (retainedState a).regs j = a.regs j := by
  unfold retainedState saveCursorState recordRepresentativeState
  rw [pushWordState_register_frame _ _ _ _ j h0 h1,
    pushWordState_register_frame _ _ _ _ j h0 h1,
    pushWordState_register_frame _ _ _ _ j h0 h1]
  exact StackRoutines.readRegs_frame a.regs 0 1 j none h0 h1

theorem descendLevelState_outside (a : State 40 896) (i : Fin 896)
    (h6 : i ≠ tupleStacks 6) (h9 : i ≠ tupleStacks 9) :
    (descendLevelState a).stacks i = a.stacks i := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h6, h9]

theorem descendLevelState_active (a : State 40 896) :
    (descendLevelState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    controllerPorts]

theorem descendClearState_cleared (a : State 40 896) :
    ∀ i ∈ currentHeadPorts, (descendClearState a).stacks i = [] := by
  intro i hi
  rw [descendClearState, clearWordsState_stacks, ite_eq_left hi]

theorem descendClearState_stack (a : State 40 896) (i : Fin 896)
    (hi : i ∉ currentHeadPorts) :
    (descendClearState a).stacks i = (descendLevelState (retainedState a)).stacks i := by
  rw [descendClearState, clearWordsState_stacks, ite_eq_right hi]

theorem descendClearState_active (a : State 40 896) :
    (descendClearState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide),
    descendLevelState_active, retainedState_register _ _ (by decide) (by decide)]


theorem counter_install_register_frame (p : CounterForPrograms.Ports 40 896)
    (a : State 40 896) (b present flag : Bool) (xs ys : List Bool) (j : Fin 40)
    (hj : ¬ ∃ i, p.register i = j) :
    (CounterForPrograms.install p a b present flag xs ys).regs j = a.regs j :=
  embedState_register_frame _ _ _ _ _ hj

theorem clearWordsTime_le_on (ports : List (Fin 896)) (a : State 40 896) (B : ℕ)
    (hb : ∀ i ∈ ports, (a.stacks i).length ≤ B) :
    clearWordsTime ports a ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing a with
  | nil => simp [clearWordsTime]
  | cons src rest ih =>
    have hsrc := hb src (by simp)
    have hrest : ∀ i ∈ rest, ((clearState src a).stacks i).length ≤ B := by
      intro i hi
      by_cases he : i = src
      · subst i
        simp [clearState]
      · simpa [clearState, he] using hb i (by simp [hi])
    have htail := ih (clearState src a) hrest
    simp only [clearWordsTime, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Recording a representative grows only the two persistent frame banks.
The tapes cleared on descent remain bounded by their original word cap. -/
theorem descend_current_bound (a : State 40 896) (F : ℕ)
    (hp : a.stacks (tupleStacks 4) = []) (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∀ i ∈ currentHeadPorts, ((descendLevelState (retainedState a)).stacks i).length ≤ F := by
  have hwords := saveCursorState_words (recordRepresentativeState a)
  have hpayload : (retainedState a).stacks (tupleStacks 4) = [] := by
    unfold retainedState saveCursorState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide),
      pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    exact (recordRepresentativeState_words a hp).2.2
  intro i hi
  have hports : i ≠ tupleStacks 0 ∧ i ≠ tupleStacks 1 ∧
      i ≠ tupleStacks 6 ∧ i ≠ tupleStacks 9 := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [descendLevelState_outside _ _ hports.2.2.1 hports.2.2.2]
  by_cases h2 : i = tupleStacks 2
  · subst i
    rw [show (retainedState a).stacks (tupleStacks 2) = [] from hwords.1]
    simp
  · by_cases h7 : i = tupleStacks 7
    · subst i
      rw [show (retainedState a).stacks (tupleStacks 7) = [] from hwords.2.1]
      simp
    · by_cases h4 : i = tupleStacks 4
      · subst i
        rw [hpayload]
        simp
      · rw [retainedState_outside a i hports.1 hports.2.1 h2 h4 h7]
        exact hframe i


/-- Current-head cleanup does not erase the newly attained child prefix or
its unary depth/address words. This also covers internal children. -/
theorem descend_ancestor_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896) (hd : depth < levels)
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4) = []) :
    AncestorStorage h key levels base (depth + 1) (Fin.snoc ancestors rep) (descendClearState a) := by
  have hf := retainFrames_state h key depth ancestors rep a
    ha.cursors ha.representatives (hw.exact rep.val.isLt) hw.remaining hp
  have heq : levels - depth = levels - (depth + 1) + 1 := by omega
  have hr : (retainedState a).stacks (tupleStacks 6) =
      List.replicate (levels - (depth + 1) + 1) true := by
    rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      ha.heads, heq]
  have hz : (retainedState a).stacks (tupleStacks 9) = List.replicate (base + depth) true := by
    rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha.address
  have hl := descendLevelState_words (retainedState a) (levels - (depth + 1)) (base + depth) hr hz
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [descendClearState_stack _ _ (by decide), hl.1]
  · rw [descendClearState_stack _ _ (by decide), hl.2.1]
    simp [Nat.add_assoc]
  · rw [descendClearState_active]
    exact ha.active

theorem resetState_outside (a : State 40 896) (i : Fin 896)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (resetState a).stacks i = a.stacks i := by
  change (initialFuelState (copyState 651 (tupleStacks 4)
    (copyState 651 (tupleStacks 2) a))).stacks i = a.stacks i
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts _ _ _ _ _ _ i h4 h7]
  simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne h4, Function.update_of_ne h2]

theorem resetGeneratorState_outside (a : State 40 896) (i : Fin 896)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7)
    (h8 : i ≠ tupleStacks 8) :
    (resetGeneratorState a).stacks i = a.stacks i := by
  change Function.update (resetState a).stacks (tupleStacks 8)
    ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) i = a.stacks i
  rw [Function.update_of_ne h8, resetState_outside a i h2 h4 h7]

theorem resetGeneratorState_cursor (a : State 40 896) (width : ℕ)
    (hh : a.stacks 651 = List.replicate width false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = [])
    (ht : a.stacks (tupleStacks 5) = []) (hi : a.stacks (tupleStacks 10) = []) :
    CursorWords (resetGeneratorState a) width 0 := by
  have hwords := resetState_words a width hh hc hp
  have hcandidate : (resetGeneratorState a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits width 0 := by
    change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) candidatePorts.counter = _
    rw [Function.update_of_ne (by decide)]
    exact resetState_assignment a width hh hc hp
  have hremaining : (resetGeneratorState a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (width + 1) (2 ^ width) := by
    change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) remainingPorts.counter = _
    rw [Function.update_of_ne (by decide)]
    exact hwords.2.1.trans (initial_remaining_word width)
  refine ⟨Nat.zero_le _, ?_, ?_, fun _ => hcandidate, ?_, ?_, ?_⟩
  · rw [hcandidate, ExecCNFTupleEnumeration.fixedBits_value _ _ (Nat.pow_pos (by decide))]
  · rw [hcandidate, ExecCNFTupleEnumeration.fixedBits_length]
    omega
  · simpa using hremaining
  · rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
    exact hi
  · rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
    exact ht

theorem resetGeneratorState_predecessor (a : State 40 896) (width : ℕ)
    (hh : a.stacks 651 = List.replicate width false)
    (hp : a.stacks (tupleStacks 8) = []) :
    (resetGeneratorState a).stacks (tupleStacks 8) = List.replicate width false := by
  change Function.update (resetState a).stacks (tupleStacks 8)
    ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 8) = _
  rw [Function.update_self, resetState_source,
    resetState_outside _ _ (by decide) (by decide) (by decide), hh, hp, List.append_nil]

theorem resetGeneratorState_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (hav : j ≠ controllerPorts.available)
    (hfresh : j ≠ controllerPorts.fresh) :
    (resetGeneratorState a).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro he; subst j; norm_num at hj
  change readRegs (resetState a).regs 0 1 none j = a.regs j
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1]
  unfold resetState
  simp only [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne hfresh, Function.update_of_ne hav]
  unfold initialFuelState
  rw [counter_install_register_frame _ _ _ _ _ _ _ j ?_]
  · exact (StackRoutines.readRegs_frame _ _ _ _ _ h0 h1).trans
      (StackRoutines.readRegs_frame _ _ _ _ _ h0 h1)
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    have hil := i.isLt
    change i.val = j.val at hv
    omega

/-- Reset follows a real matrix load. It preserves the attained ancestor
frames and prepares exactly the first numeric assignment for this head. -/
theorem reset_scan_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (a : State 40 896)
    (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hl : a.regs controllerPorts.leaf = false)
    (hh : a.stacks 651 = List.replicate (h depth.val) false)
    (hc : a.stacks (tupleStacks 2) = []) (hk : a.stacks (tupleStacks 3) = [])
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hz : a.stacks (tupleStacks 8) = []) (hi : a.stacks (tupleStacks 10) = []) :
    ScanStorage h key levels base depth ancestors 0 (resetGeneratorState a) := by
  have hf (i : Fin 896) (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4)
      (h7 : i ≠ tupleStacks 7) (h8 : i ≠ tupleStacks 8) :
      (resetGeneratorState a).stacks i = a.stacks i :=
    resetGeneratorState_outside a i h2 h4 h7 h8
  refine ⟨⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩,
    resetGeneratorState_cursor a (h depth.val) hh hc hp ht hi, ?_, ?_, ?_,
    resetGeneratorState_predecessor a (h depth.val) hh hz⟩
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.cursors
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.representatives
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.heads
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.address
  · rw [resetGeneratorState_register_frame _ _ (by decide) (by decide) (by decide)]
    exact ha.active
  · rw [resetGeneratorState_register_frame _ _ (by decide) (by decide) (by decide)]
    exact hl
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact hk
  · change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 4) = []
    rw [Function.update_of_ne (by decide)]
    exact (resetState_words a (h depth.val) hh hc hp).2.2

/-- Composition for an internal descent uses the supplied actual loader
evaluation, then the concrete power-of-two cursor initializer. -/
theorem descend_internal_eval (loadHead : Cmd 40 896) (a loaded : State 40 896)
    (width candidate childWidth loadSteps : ℕ)
    (hc : a.stacks (tupleStacks 2) = ExecCNFTupleEnumeration.fixedBits width candidate)
    (hn : a.stacks (tupleStacks 7) =
      ExecCNFTupleEnumeration.fixedBits (width + 1) (2 ^ width - candidate))
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hl : (descendClearState a).regs controllerPorts.leaf = false)
    (hload : Eval loadHead loadSteps (descendClearState a) loaded)
    (hwidth : loaded.stacks 651 = List.replicate childWidth false)
    (hremaining : loaded.stacks (tupleStacks 7) = [])
    (hscratch : loaded.stacks (tupleStacks 5) = [])
    (hpayload : loaded.stacks (tupleStacks 4) = []) :
    Eval (descendWith loadHead)
      (22 * width + 25 * childWidth + loadSteps +
        clearWordsTime currentHeadPorts (descendLevelState (retainedState a)) + 53)
      a (resetGeneratorState loaded) := by
  have hf := retainFrames_eval width candidate a hc hn hp ht
  have hreset := resetGenerator_eval loaded childWidth hwidth hremaining hscratch hpayload
  have hbranch : Eval (.ite controllerPorts.leaf (.base .skip)
      (.seq loadHead resetGeneratorCommand)) (loadSteps + (25 * childWidth + 22) + 1)
      (descendClearState a) (resetGeneratorState loaded) := .ite_false hl (hload.seq hreset)
  generalize hcost : 22 * width + 25 = frameSteps at hf
  cases hf with
  | seq hrecord hsave =>
    have hall := hrecord.seq (hsave.seq ((descendLevel_eval (retainedState a)).seq
      ((clearWords_eval currentHeadPorts (descendLevelState (retainedState a))).seq hbranch)))
    change Eval (descendWith loadHead) _ a (resetGeneratorState loaded) at hall
    convert hall using 1
    all_goals try with_reducible_and_instances rfl
    omega

theorem descend_internal_leaf_flag (a : State 40 896) (remaining address : ℕ)
    (hpositive : 0 < remaining)
    (hh : a.stacks (tupleStacks 6) = List.replicate (remaining + 1) true)
    (hz : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendClearState a).regs controllerPorts.leaf = false := by
  have hw := descendLevelState_words (retainedState a) remaining address
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hh)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz)
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide), hw.2.2]
  simp only [Nat.ne_of_gt hpositive, decide_false]

theorem descendClearState_outside_tuple (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) : (descendClearState a).stacks i = a.stacks i := by
  have hc : i ∉ currentHeadPorts := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨hi 2, hi 3, hi 4, hi 5, hi 7, hi 8, hi 10, hi 11⟩
  rw [descendClearState_stack a i hc, descendLevelState_outside _ _ (hi 6) (hi 9),
    retainedState_outside _ _ (hi 0) (hi 1) (hi 2) (hi 4) (hi 7)]

theorem reset_candidate_ready (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h : ℕ)
    (hW : a.stacks 141 = W)
    (hrows : a.stacks 847 = Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words))
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hs : a.stacks (tupleStacks 3) = [])
    (hp : a.stacks (tupleStacks 4) = []) (hpred : a.stacks (tupleStacks 8) = [])
    (hscratch : ∀ i : Fin 24, i ≠ 0 → i ≠ 15 → i ≠ 16 → i ≠ 17 → i ≠ 18 → i ≠ 22 →
      a.stacks (rescanStacks i) = []) :
    CandidateReady (resetGeneratorState a) W rows h ⟨0, Nat.pow_pos (by decide)⟩ := by
  have outside (i : Fin 24) (h16 : i ≠ 16) (h18 : i ≠ 18) :
      (resetGeneratorState a).stacks (rescanStacks i) = a.stacks (rescanStacks i) := by
    apply resetGeneratorState_outside <;> fin_cases i <;> first | contradiction | decide
  have hzero : List.replicate h false = ExecCNFTupleEnumeration.fixedBits h 0 :=
    (resetState_words a h hw hc hp).1.symm.trans (resetState_assignment a h hw hc hp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [outside 0 (by decide) (by decide)]
    exact hW
  · rw [outside 15 (by decide) (by decide)]
    exact hrows
  · change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 2) = _
    rw [Function.update_of_ne (by decide)]
    exact resetState_assignment a h hw hc hp
  · rw [outside 17 (by decide) (by decide)]
    exact hs
  · rw [rescanStacks_predecessor, resetGeneratorState_predecessor a h hw hpred]
    exact hzero
  · intro i h0 h15 h16 h17 h18 h22
    rw [outside i h16 h18]
    exact hscratch i h0 h15 h16 h17 h18 h22


theorem reset_endpoint_bound (a : State 40 896) (h F : ℕ)
    (hh : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = [])
    (ht : a.stacks (tupleStacks 5) = []) (hz : a.stacks (tupleStacks 8) = [])
    (hi : a.stacks (tupleStacks 10) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hwidth : h + 1 ≤ F) :
    ∀ i, ((resetGeneratorState a).stacks i).length ≤ F := by
  have hw := resetGeneratorState_cursor a h hh hc hp ht hi
  intro i
  by_cases h2 : i = tupleStacks 2
  · subst i
    exact hw.width.trans hwidth
  · by_cases h4 : i = tupleStacks 4
    · subst i
      change (Function.update (resetState a).stacks (tupleStacks 8)
        ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 4)).length ≤ F
      rw [Function.update_of_ne (by decide), (resetState_words a h hh hc hp).2.2]
      simp
    · by_cases h7 : i = tupleStacks 7
      · subst i
        rw [show (resetGeneratorState a).stacks (tupleStacks 7) = _ from hw.remaining,
          ExecCNFTupleEnumeration.fixedBits_length]
        exact hwidth
      · by_cases h8 : i = tupleStacks 8
        · subst i
          rw [resetGeneratorState_predecessor a h hh hz, List.length_replicate]
          omega
        · rw [resetGeneratorState_outside a i h2 h4 h7 h8]
          exact hframe i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem result_high_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
    (result s z frame rp rm rs raw shifted).stacks i=frame.stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id i).trans
    (SignatureHeadLoader.lowResultFrom_frame headAddress _ _ i hi hne)

theorem result_register_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 40) (hi : 16 ≤ i.val) :
    (result s z frame rp rm rs raw shifted).regs i=frame.regs i :=
  SignatureHeadLoader.leafOutputFrom_registers headAddress frame _ i hi

theorem result_low (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks i)=
      (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom headAddress frame)
        rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id (SignatureHeadLoader.lowStacks i)).trans
    (SignatureHeadLoader.lowResultFrom_low headAddress _ _ i h659 h668 h669)

theorem result_offset (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 141=frame.stacks 141 := by
  rw [show (141 : Fin 896)=SignatureHeadLoader.lowStacks 141 from rfl,
    result_low s z frame rp rm rs raw shifted 141 (by decide) (by decide) (by decide)]
  rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ 141
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact SignatureHeadLoader.addressStateFrom_frame headAddress _ 141 (by decide)

theorem result_matrix (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 847=
      Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words) := by
  rw [result, SignatureHeadLoader.leafOutputFrom_matrix]
  exact SignatureHeadLoader.localResult_matrixWord ..

theorem result_raw_empty (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 846=[] :=
  SignatureHeadLoader.leafOutputFrom_raw_empty headAddress frame _

/-- Every local rescan scratch word is blank after actual matrix staging. -/
theorem result_rescan_scratch (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 24) (h0 : i≠0) (h15 : i≠15) (h16 : i≠16) (h17 : i≠17)
    (h18 : i≠18) (_h22 : i≠22) :
    (result s z frame rp rm rs raw shifted).stacks (rescanStacks i)=[] := by
  have hoff : rescanStacks i=SignatureHeadLoader.lowStacks
      (workPort (by decide) (⟨i.val, by omega⟩ : Fin 288)) := by
    fin_cases i <;> first | contradiction | rfl
  have hne (q : Fin 768) (hq : 628 ≤ q.val) :
      workPort (by decide) (⟨i.val, by omega⟩ : Fin 288)≠q := by
    intro he
    have hv := congrArg Fin.val he
    change 340+i.val=q.val at hv
    have := i.isLt
    omega
  rw [hoff, result_low s z frame rp rm rs raw shifted _
    (hne 659 (by decide)) (hne 668 (by decide)) (hne 669 (by decide))]
  exact SignatureHeadLoader.localResult_work_empty ..

/-- The physically emitted full integer matrix initializes the actual
predecessor scanner at its zero candidate, including empty heads. -/
theorem result_reset_ready (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hc : frame.stacks (tupleStacks 2)=[]) (hk : frame.stacks (tupleStacks 3)=[])
    (hp : frame.stacks (tupleStacks 4)=[]) (hz : frame.stacks (tupleStacks 8)=[]) :
    CandidateReady (resetGeneratorState (result s z frame rp rm rs raw shifted))
      (frame.stacks 141) shifted (selectedHeads s.n s.rows s.low z).length
      ⟨0, Nat.pow_pos (by decide)⟩ := by
  apply reset_candidate_ready
  · exact result_offset ..
  · exact result_matrix ..
  · exact result_headsize ..
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 2)
      (by decide) (by decide)).trans hc
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 3)
      (by decide) (by decide)).trans hk
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 4)
      (by decide) (by decide)).trans hp
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 8)
      (by decide) (by decide)).trans hz
  · exact result_rescan_scratch s z frame rp rm rs raw shifted


section Storage
open SignatureTupleDFS SignatureTupleTraversal

/-- Reloading a head preserves the complete attained ancestor path. -/
theorem result_ancestor_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth)
    (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth ancestors frame) :
    AncestorStorage h key levels base depth ancestors
      (result s z frame rp rm rs raw shifted) := by
  refine ⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 0) (by decide) (by decide)]
    exact ha.cursors
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 1) (by decide) (by decide)]
    exact ha.representatives
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 6) (by decide) (by decide)]
    exact ha.heads
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 9) (by decide) (by decide)]
    exact ha.address
  · rw [result_register_frame s z frame rp rm rs raw shifted controllerPorts.active (by decide)]
    exact ha.active

/-- A completed reload followed by the actual bounded counter initializer
establishes the next head's concrete scan boundary. -/
theorem result_reset_scan_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val)
    (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth.val ancestors frame)
    (hl : frame.regs controllerPorts.leaf=false)
    (hh : (selectedHeads s.n s.rows s.low z).length=h depth.val)
    (hc : frame.stacks (tupleStacks 2)=[]) (hk : frame.stacks (tupleStacks 3)=[])
    (hp : frame.stacks (tupleStacks 4)=[]) (ht : frame.stacks (tupleStacks 5)=[])
    (hz : frame.stacks (tupleStacks 8)=[]) :
    ScanStorage h key levels base depth ancestors 0
      (resetGeneratorState (result s z frame rp rm rs raw shifted)) := by
  apply reset_scan_storage h key levels base depth ancestors
  · exact result_ancestor_storage h key levels base depth.val ancestors s z frame rp rm rs raw shifted ha
  · rw [result_register_frame s z frame rp rm rs raw shifted controllerPorts.leaf (by decide)]
    exact hl
  · rw [result_headsize, hh]
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 2)
      (by decide) (by decide)).trans hc
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 3)
      (by decide) (by decide)).trans hk
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 4)
      (by decide) (by decide)).trans hp
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 5)
      (by decide) (by decide)).trans ht
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 8)
      (by decide) (by decide)).trans hz
  · exact result_raw_empty ..


/-- Internal descent retains only attained frames and the unary depth. Its
boundary bound depends on depth and word lengths, never on visited nodes. -/
theorem descend_endpoint_bound (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth hmax F : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896) (hd : depth<levels)
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4)=[])
    (hh : ∀ d<levels, h d≤hmax)
    (hcap : 6*levels*(hmax+1)+(base+levels)≤F)
    (hframe : ∀ i, (a.stacks i).length≤F) :
    ∀ i, ((descendClearState a).stacks i).length≤F := by
  have hb := descend_ancestor_storage h key levels base depth ancestors rep a hd ha hw hp
  have hf := hb.frame_bound h key hmax hh
  have hcleared := descendClearState_cleared a
  intro i
  by_cases hi : ∃ j : Fin 12, i=tupleStacks j
  · obtain ⟨j,rfl⟩ := hi
    fin_cases j
    · change ((descendClearState a).stacks (tupleStacks 0)).length≤F
      omega
    · change ((descendClearState a).stacks (tupleStacks 1)).length≤F
      omega
    · change ((descendClearState a).stacks (tupleStacks 2)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 3)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 4)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 5)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 6)).length≤F
      rw [hb.heads, List.length_replicate]
      omega
    · change ((descendClearState a).stacks (tupleStacks 7)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 8)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 9)).length≤F
      rw [hb.address, List.length_replicate]
      omega
    · change ((descendClearState a).stacks (tupleStacks 10)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 11)).length≤F
      rw [hcleared _ (by decide)]; simp
  · rw [descendClearState_outside_tuple a i (fun j hj => hi ⟨j,hj⟩)]
    exact hframe i


private theorem low_outside_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  have := i.isLt
  omega


/-- An attained internal child is reached by actual frame pushes, cleanup,
head loading and bounded counter setup, with the same retained cap F. -/
theorem descend_native_run_oai (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (hd : depth+1<levels)
    (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
    (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hcaches : CacheCorrect s.height (unary s.R) s.width words)
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hanc : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4)=[])
    (F L hmax : ℕ) (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
    (hh : ∀ d<levels,h d≤hmax)
    (hcap : 6*levels*(hmax+1)+(base+levels)+(hmax+1)≤F)
    (hsize : (selectedHeads s.n s.rows s.low (base+(depth+1))).length=h (depth+1)) :
    ∃ rp rm rs raw shifted total,
      let loaded := result s (base+(depth+1)) (descendClearState a) rp rm rs raw shifted
      let finish := resetGeneratorState loaded
      Eval (descendWith loadHead) total a finish ∧
      total+1 ≤ runEnvelope B F+100*F+100 ∧ WordBound F finish ∧
      ScanStorage h key levels base ⟨depth+1,hd⟩ (Fin.snoc ancestors rep) 0 finish ∧
      CandidateReady finish (a.stacks 141) shifted (h (depth+1)) ⟨0,Nat.pow_pos (by decide)⟩ ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low (base+(depth+1))) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (descendWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (descendWith loadHead) 0 0).entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F := by
  let b := descendClearState a
  have hbanc := descend_ancestor_storage h key levels base depth ancestors rep a (by omega) hanc hw hp
  have hb := descend_endpoint_bound h key levels base depth hmax F ancestors rep a (by omega)
    hanc hw hp hh (by omega) hf
  have hbm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
    constructor
    intro i hi
    exact (descendClearState_outside_tuple a (SignatureHeadLoader.lowStacks i)
      (low_outside_tuple i)).trans (hm.stored i hi)
  have hbW : b.stacks 141=a.stacks 141 :=
    descendClearState_outside_tuple a 141 (low_outside_tuple 141)
  have hblank := descendClearState_cleared a
  obtain ⟨rp,rm,rs,raw,shifted,loadSteps,hload,hloadTime,hloaded,hraw,hshift,_⟩ :=
    load_run_polynomial s source ha B hB hrows ra rd rc words hcaches b hbm (base+(depth+1)) F L
      hbanc.address hb (by simpa only [hbW] using hW) hout
  let loaded := result s (base+(depth+1)) b rp rm rs raw shifted
  have hhigh (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
      loaded.stacks i=b.stacks i := result_high_frame s (base+(depth+1)) b rp rm rs raw shifted i hi hne
  have hwidth : loaded.stacks 651=List.replicate (h (depth+1)) false := by rw [result_headsize,hsize]
  have hremaining : loaded.stacks (tupleStacks 7)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide))
  have hscratch : loaded.stacks (tupleStacks 5)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide))
  have hpayload : loaded.stacks (tupleStacks 4)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide))
  have hl : b.regs controllerPorts.leaf=false := descend_internal_leaf_flag a
    (levels-(depth+1)) (base+depth) (by omega)
    (by rw [hanc.heads]; congr 1; omega) hanc.address
  have he := descend_internal_eval loadHead a loaded (h depth) rep.val.val (h (depth+1)) loadSteps
    (hw.exact rep.val.isLt) hw.remaining hp hw.decrementScratch hl hload hwidth
    hremaining hscratch hpayload
  have hscan := result_reset_scan_storage h key levels base ⟨depth+1,hd⟩ (Fin.snoc ancestors rep)
    s (base+(depth+1)) b rp rm rs raw shifted hbanc hl hsize
    (hblank _ (by decide)) (hblank _ (by decide)) (hblank _ (by decide))
    (hblank _ (by decide)) (hblank _ (by decide))
  have hready := result_reset_ready s (base+(depth+1)) b rp rm rs raw shifted
    (hblank _ (by decide)) (hblank _ (by decide)) (hblank _ (by decide)) (hblank _ (by decide))
  rw [hbW,hsize] at hready
  rw [hbW] at hshift
  have hchild : h (depth+1)+1≤F := by have := hh (depth+1) hd; omega
  have hend := reset_endpoint_bound loaded (h (depth+1)) F hwidth
    ((hhigh _ (by decide) (by decide)).trans (hblank _ (by decide))) hpayload hscratch
    ((hhigh _ (by decide) (by decide)).trans (hblank _ (by decide)))
    (result_raw_empty s (base+(depth+1)) b rp rm rs raw shifted) hloaded hchild
  have hclear := clearWordsTime_le_on currentHeadPorts _ F (descend_current_bound a F hp hf)
  change clearWordsTime currentHeadPorts _≤8*(2*F+3) at hclear
  have hcurrent := hh depth (by omega)
  have htime : 22*h depth+25*h (depth+1)+loadSteps+
      clearWordsTime currentHeadPorts (descendLevelState (SignatureTupleRefinement.retainedState a))+53+1≤
      runEnvelope B F+100*F+100 := by omega
  refine ⟨rp,rm,rs,raw,shifted,_,he,htime,hend,hscan,hready,hraw,hshift,?_⟩
  have hpref := StructuredSpace.local_stack_bound (compiled (descendWith loadHead) 0 0)
    (a := a.withPC (some (compiled (descendWith loadHead) 0 0).entry))
    (steps := runEnvelope B F+100*F+100) (StreamResources.dataBits_le_mul _ hf)
  intro p q hpn hq i
  exact (hpref p q (by omega) hq i).trans (by omega)


end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.descend_native_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.descend_native_run_oai.{u_1}
