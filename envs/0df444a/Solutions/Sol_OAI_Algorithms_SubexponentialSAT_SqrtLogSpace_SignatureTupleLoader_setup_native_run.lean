-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:02:31.388052+00:00
-- url     : https://prove2.me/submissions/67203c82-6c8d-4d7c-a6f0-78e6c4f8d788

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_load_run_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_result_headsize
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem selectedHeads_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedHeads n rows low z).length ≤ n :=
  HeadIdentifierProgram.count_le _ _

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the paid interpolation cache for the later source-polynomial
worker. These three copies are charged before the private head bank is cleared. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem retainedState_frame (a : Data) (i : Fin 768)
    (h659 : i≠659) (h710 : i≠710) (h711 : i≠711) (h712 : i≠712) :
    (retainedState a).stacks i=a.stacks i := by
  rw [retainedState,copyMany_frame]
  · simp [clearMany_stacks,retainedPorts,h659]
  · simp [retainedCopies,h710,h711,h712]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact state and cost of the paid per-node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog
namespace LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem addressState_frame (a : Data) (regs : Fin 3 → Bool) (r t : ℕ) (i : Fin 768)
    (hi : Protected i) (h648 : i≠648) (h649 : i≠649) :
    (addressState a regs r t).stacks i=a.stacks i := by
  apply returned_frame addressRegs (by decide) addressInputs addressOutputs a _ i hi
  intro p hp
  simp only [addressOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · exact h648
  · exact h649

theorem countedState_frame (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool))
    (i : Fin 768) (hi : Protected i) (h647 : i≠647) :
    (countedState a regs records).stacks i=a.stacks i := by
  apply returned_frame rowCountRegs (by decide) rowCountInputs rowCountOutputs a _ i hi
  intro p hp
  simp only [rowCountOutputs,List.mem_singleton] at hp
  subst p
  exact h647

theorem bootState_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649] : List (Fin 768))) :
    (bootState a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  rcases hne with ⟨h640,h641,h642,h643,h647,h648,h649⟩
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ i hi,
    countedState_frame _ _ _ _ hi h647,addressState_frame _ _ _ _ _ hi h648 h649]
  intro p hp
  simp only [cacheOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact h640
  · exact h641
  · exact h642
  · exact h643

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Initialization of one node's physical Cartesian head loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem nodeStart_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649,660,665,710,711,712] : List (Fin 768))) :
    (nodeStart a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  have h659 : i≠659 := hi.2
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  obtain ⟨h640,h641,h642,h643,h647,h648,h649,h660,h665,h710,h711,h712⟩ := hne
  simp only [nodeStart,tupleInitialized,Function.update_of_ne h665,Function.update_of_ne h660]
  rw [retainedState_frame _ i h659 h710 h711 h712]
  apply bootState_frame a ra rd rc r t records height R width words i hi
  simp [h640,h641,h642,h643,h647,h648,h649]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native entry cache is the actual output of the paid node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open RowSelectionProgram

theorem start_low (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) : (start s a ra rd rc words).stacks i=a.stacks i := by
  apply nodeStart_frame
  · constructor
    · left; exact hi
    · intro h; have hh := congrArg Fin.val h; simp [temporary] at hh; omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
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

theorem initializeLevels_eval (a : State 40 896) (hs : a.stacks (tupleStacks 5) = []) :
    Eval initializeLevelsCommand
      (7 * (a.stacks 130).length + 7 * (a.stacks 649).length + 13)
      a (initializeLevelsState a) := by
  let b := copyState 130 (tupleStacks 6) a
  have hb := copyWord_eval 130 (tupleStacks 6) (tupleStacks 5)
    (by decide) (by decide) (by decide) a hs
  have hbs : b.stacks (tupleStacks 5) = [] := by
    simpa [b, copyState, StackRoutines.copyStacks] using hs
  have hc := copyWord_eval 649 (tupleStacks 9) (tupleStacks 5)
    (by decide) (by decide) (by decide) b hbs
  have ht := Eval.seq hb (Eval.seq hc
    (Eval.base (StructuredProgram.Eval.seq (.atom (.peek (tupleStacks 6) 0 1) _)
      (.seq (.atom (.bnot controllerPorts.leaf 1) _)
        (.atom (.set controllerPorts.active true) _)))))
  have hw : b.stacks 649 = a.stacks 649 := by
    simp [b, copyState, StackRoutines.copyStacks, (by decide : (649 : Fin 896) ≠ tupleStacks 6)]
  rw [hw] at ht
  change Eval initializeLevelsCommand _ a (initializeLevelsState a) at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem initializeLevelsState_words (a : State 40 896) (heads address : ℕ)
    (hh : a.stacks 130 = List.replicate heads true)
    (ha : a.stacks 649 = List.replicate address true)
    (he : a.stacks (tupleStacks 6) = []) (hz : a.stacks (tupleStacks 9) = []) :
    (initializeLevelsState a).stacks (tupleStacks 6) = List.replicate heads true ∧
      (initializeLevelsState a).stacks (tupleStacks 9) = List.replicate address true := by
  change (copyState 649 (tupleStacks 9) (copyState 130 (tupleStacks 6) a)).stacks
      (tupleStacks 6) = _ ∧
    (copyState 649 (tupleStacks 9) (copyState 130 (tupleStacks 6) a)).stacks
      (tupleStacks 9) = _
  simp [copyState, StackRoutines.copyStacks, hh, ha, he, hz,
    (by decide : tupleStacks 6 ≠ tupleStacks 9),
    (by decide : tupleStacks 9 ≠ tupleStacks 6),
    (by decide : (649 : Fin 896) ≠ tupleStacks 6)]

theorem initializeLevelsState_flags (a : State 40 896) (heads : ℕ)
    (hh : a.stacks 130 = List.replicate heads true)
    (he : a.stacks (tupleStacks 6) = []) :
    (initializeLevelsState a).regs controllerPorts.active = true ∧
      (initializeLevelsState a).regs controllerPorts.leaf = decide (heads = 0) := by
  cases heads <;>
    simp [initializeLevelsState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      copyState, StackRoutines.copyStacks, controllerPorts, hh, he, List.replicate_succ,
      (by decide : tupleStacks 6 ≠ tupleStacks 9)]

theorem initial_remaining_word (h : ℕ) :
    List.replicate h false ++ [true] =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h) := by
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have hb : 2 ^ h < 2 ^ (h + 1) := by rw [pow_succ]; omega
  exact ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
    (by rw [Counters.powerTwo_value, ExecCNFTupleEnumeration.fixedBits_value _ _ hb])

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

theorem initialClearState_tuple (a : State 40 896) (i : Fin 12) :
    (initialClearState a).stacks (tupleStacks i) = [] := by
  rw [initialClearState, clearWordsState_stacks,
    ite_eq_left (List.mem_ofFn.mpr ⟨i, rfl⟩)]

theorem initialClearState_source130 (a : State 40 896) :
    (initialClearState a).stacks 130 = a.stacks 130 := by
  rw [initialClearState, clearWordsState_stacks, ite_eq_right (by decide)]

theorem initialClearState_source649 (a : State 40 896) :
    (initialClearState a).stacks 649 = a.stacks 649 := by
  rw [initialClearState, clearWordsState_stacks, ite_eq_right (by decide)]

theorem initialControlState_tuple (a : State 40 896) (i : Fin 12)
    (h6 : i ≠ 6) (h9 : i ≠ 9) :
    (initialControlState a).stacks (tupleStacks i) = [] := by
  have he6 : tupleStacks i ≠ tupleStacks 6 := fun he => h6 (tupleStacks.injective he)
  have he9 : tupleStacks i ≠ tupleStacks 9 := fun he => h9 (tupleStacks.injective he)
  change (copyState 649 (tupleStacks 9)
    (copyState 130 (tupleStacks 6) (initialClearState a))).stacks (tupleStacks i) = []
  simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne he9, Function.update_of_ne he6]
  exact initialClearState_tuple a i

theorem initialControlState_flags (a : State 40 896) (levels : ℕ)
    (hh : a.stacks 130 = List.replicate levels true) :
    (initialControlState a).regs controllerPorts.active = true ∧
      (initialControlState a).regs controllerPorts.leaf = decide (levels = 0) :=
  initializeLevelsState_flags (initialClearState a) levels
    ((initialClearState_source130 a).trans hh) (initialClearState_tuple a 6)

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

/-- Positive-depth setup reaches the first head through its actual loader
run and the fixed bounded-memory initializer. -/
theorem setup_loaded_run_space (loadHead : Cmd 40 896) (a loaded : State 40 896)
    (levels base h F loadSteps : ℕ) (hlevels : 0 < levels)
    (hheads : a.stacks 130 = List.replicate levels true)
    (hbase : a.stacks 649 = List.replicate base true)
    (hload : Eval loadHead loadSteps (initialControlState a) loaded)
    (hh : loaded.stacks 651 = List.replicate h false)
    (hc : loaded.stacks (tupleStacks 2) = []) (hp : loaded.stacks (tupleStacks 4) = [])
    (ht : loaded.stacks (tupleStacks 5) = []) (hr : loaded.stacks (tupleStacks 7) = [])
    (hz : loaded.stacks (tupleStacks 8) = []) (hi : loaded.stacks (tupleStacks 10) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F)
    (hloaded : ∀ i, (loaded.stacks i).length ≤ F) (hcursor : h + 1 ≤ F) :
    ∃ n,
      Eval (setupWith loadHead) n a (resetGeneratorState loaded) ∧
      (∀ i, ((resetGeneratorState loaded).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (setupWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1) + loadSteps) ∧
      n + 1 ≤ loadSteps + 63 * F + 73 := by
  have hinit := initializeLevels_eval (initialClearState a) (initialClearState_tuple a 5)
  rw [initialClearState_source130, initialClearState_source649, hheads, hbase,
    List.length_replicate, List.length_replicate] at hinit
  have hl : (initialControlState a).regs controllerPorts.leaf = false := by
    rw [(initialControlState_flags a levels hheads).2]
    simp only [Nat.ne_of_gt hlevels, decide_false]
  have hreset := resetGenerator_eval loaded h hh hr ht hp
  have hb : Eval (.ite controllerPorts.leaf (.base .skip) (.seq loadHead resetGeneratorCommand))
      (loadSteps + (25 * h + 22) + 1) (initialControlState a) (resetGeneratorState loaded) :=
    .ite_false hl (hload.seq hreset)
  have he := (clearWords_eval (List.ofFn tupleStacks) a).seq (hinit.seq hb)
  change Eval (setupWith loadHead) _ a (resetGeneratorState loaded) at he
  have hclear := clearWordsTime_le_on (List.ofFn tupleStacks) a F (fun i _ => hframe i)
  rw [List.length_ofFn] at hclear
  have hlevelsF := hframe 130
  have hbaseF := hframe 649
  rw [hheads, List.length_replicate] at hlevelsF
  rw [hbase, List.length_replicate] at hbaseF
  have hn : clearWordsTime (List.ofFn tupleStacks) a +
      (7 * levels + 7 * base + 13 + (loadSteps + (25 * h + 22) + 1)) + 1 ≤
      loadSteps + 63 * F + 73 := by omega
  refine ⟨_, he, reset_endpoint_bound loaded h F hh hc hp ht hz hi hloaded hcursor, ?_, hn⟩
  have hs := StructuredSpace.local_stack_bound (compiled (setupWith loadHead) 0 0)
    (a := a.withPC (some (compiled (setupWith loadHead) 0 0).entry))
    (steps := loadSteps + 63 * F + 73) (StreamResources.dataBits_le_mul _ hframe)
  intro p q hp hq i
  exact (hs p q (by omega) hq i).trans (by omega)

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


/-- The fixed retained output envelope also pays the extra leading bit of
an exact power-of-two remaining-assignment word. -/
theorem retainedOutputBound_headroom (n N D B L : ℕ) :
    n+1≤SignatureHeadLoader.retainedOutputBound n N D B L := by
  have hn : n≤n*(2*n+2) := by
    calc
      n=n*1 := (Nat.mul_one _).symm
      _≤n*(2*n+2) := Nat.mul_le_mul_left n (by omega)
  unfold SignatureHeadLoader.retainedOutputBound
  omega

section Storage
open SignatureTupleDFS SignatureTupleTraversal


theorem initialControlState_outside_tuple (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i≠tupleStacks j) :
    (initialControlState a).stacks i=a.stacks i := by
  change (SignatureTupleProgram.copyState 649 (tupleStacks 9) (SignatureTupleProgram.copyState 130 (tupleStacks 6)
    (initialClearState a))).stacks i=_
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (hi 9),
    Function.update_of_ne (hi 6)]
  rw [initialClearState,clearWordsState_stacks,ite_eq_right]
  intro hm
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
  exact hi j hj.symm

/-- Initializing controller words restores the input cap before the first
matrix loader is invoked. -/
theorem initialControl_endpoint_bound (a : State 40 896) (levels base F : ℕ)
    (hh : a.stacks 130=List.replicate levels true)
    (hz : a.stacks 649=List.replicate base true)
    (hframe : ∀ i, (a.stacks i).length≤F) :
    ∀ i, ((initialControlState a).stacks i).length≤F := by
  have hwords := initializeLevelsState_words (initialClearState a) levels base
    ((initialClearState_source130 a).trans hh) ((initialClearState_source649 a).trans hz)
    (initialClearState_tuple a 6) (initialClearState_tuple a 9)
  have hl := hframe 130
  have hb := hframe 649
  rw [hh,List.length_replicate] at hl
  rw [hz,List.length_replicate] at hb
  intro i
  by_cases hi : ∃ j : Fin 12, i=tupleStacks j
  · obtain ⟨j,rfl⟩ := hi
    by_cases h6 : j=6
    · subst j
      change ((initializeLevelsState (initialClearState a)).stacks (tupleStacks 6)).length≤F
      rw [hwords.1,List.length_replicate]
      exact hl
    by_cases h9 : j=9
    · subst j
      change ((initializeLevelsState (initialClearState a)).stacks (tupleStacks 9)).length≤F
      rw [hwords.2,List.length_replicate]
      exact hb
    rw [initialControlState_tuple a j h6 h9,List.length_nil]
    exact Nat.zero_le _
  · rw [initialControlState_outside_tuple a i (fun j hj => hi ⟨j,hj⟩)]
    exact hframe i


private theorem low_outside_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  have := i.isLt
  omega

theorem initialControl_masters (a : State 40 896) (base : Data)
    (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (initialControlState a)) := by
  constructor
  intro i hi
  exact (initialControlState_outside_tuple a (SignatureHeadLoader.lowStacks i)
    (low_outside_tuple i)).trans (hm.stored i hi)


/-- The first positive-depth scan is reached by the actual fixed setup,
actual native head loader, and actual bounded counter initializer. -/
theorem setup_native_run_oai (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
    (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (base F L : ℕ) (hbase : a.stacks 649=unary base) (hpositive : 0 < s.r)
    (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval (setupWith loadHead) total a
        (resetGeneratorState (result s base (initialControlState a) rp rm rs raw shifted)) ∧
      total+1 ≤ runEnvelope B F+63*F+73 ∧
      WordBound F (resetGeneratorState
        (result s base (initialControlState a) rp rm rs raw shifted)) ∧
      CandidateReady (resetGeneratorState
        (result s base (initialControlState a) rp rm rs raw shifted))
        (a.stacks 141) shifted (selectedHeads s.n s.rows s.low base).length
        ⟨0,Nat.pow_pos (by decide)⟩ ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low base) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (setupWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F := by
  have hheads : a.stacks 130=unary s.r :=
    (hm.stored 130 (by decide)).trans
      ((Native.start_low s source ra rd rc words 130 (by decide)).trans ha.colors)
  let b := initialControlState a
  have hb : WordBound F b := initialControl_endpoint_bound a s.r base F hheads hbase hf
  have hbm := initialControl_masters a _ hm
  have haddr : b.stacks headAddress=unary base := by
    exact (initializeLevelsState_words (initialClearState a) s.r base
      ((initialClearState_source130 a).trans hheads) ((initialClearState_source649 a).trans hbase)
      (initialClearState_tuple a 6) (initialClearState_tuple a 9)).2
  have hbW : b.stacks 141=a.stacks 141 :=
    initialControlState_outside_tuple a 141 (low_outside_tuple 141)
  have hblank (i : Fin 12) (h6 : i≠6) (h9 : i≠9) : b.stacks (tupleStacks i)=[] :=
    initialControlState_tuple a i h6 h9
  obtain ⟨rp,rm,rs,raw,shifted,loadSteps,hload,hloadTime,hloaded,hraw,hshift,_⟩ :=
    load_run_polynomial s source ha B hB hrows ra rd rc words hw b hbm base F L haddr hb
      (by simpa only [hbW] using hW) hout
  let loaded := result s base b rp rm rs raw shifted
  have hhigh (i : Fin 12) (hi : i≠10) (hj : i≠11) : loaded.stacks (tupleStacks i)=b.stacks (tupleStacks i) := by
    apply result_high_frame
    · change 768≤836+i.val; omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      constructor
      · intro he
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val he
        change 836+i.val=846 at hv
        omega
      · intro he
        apply hj
        apply Fin.ext
        have hv := congrArg Fin.val he
        change 836+i.val=847 at hv
        omega
  have hh := result_headsize s base b rp rm rs raw shifted
  have hwidth : (selectedHeads s.n s.rows s.low base).length+1≤F :=
    (Nat.add_le_add_right (Bounds.selectedHeads_length s.n s.rows s.low base) 1).trans
      ((retainedOutputBound_headroom s.n s.N s.D s.columnLength L).trans hout)
  obtain ⟨total,he,hend,hprefix,ht⟩ := setup_loaded_run_space loadHead a loaded
    s.r base (selectedHeads s.n s.rows s.low base).length F loadSteps hpositive hheads hbase hload hh
    ((hhigh 2 (by decide) (by decide)).trans (hblank 2 (by decide) (by decide)))
    ((hhigh 4 (by decide) (by decide)).trans (hblank 4 (by decide) (by decide)))
    ((hhigh 5 (by decide) (by decide)).trans (hblank 5 (by decide) (by decide)))
    ((hhigh 7 (by decide) (by decide)).trans (hblank 7 (by decide) (by decide)))
    ((hhigh 8 (by decide) (by decide)).trans (hblank 8 (by decide) (by decide)))
    (result_raw_empty s base b rp rm rs raw shifted) hf hloaded hwidth
  have ready := result_reset_ready s base b rp rm rs raw shifted
    (hblank 2 (by decide) (by decide)) (hblank 3 (by decide) (by decide))
    (hblank 4 (by decide) (by decide)) (hblank 8 (by decide) (by decide))
  rw [hbW] at ready hshift
  refine ⟨rp,rm,rs,raw,shifted,total,he,by omega,hend,ready,hraw,hshift,?_⟩
  intro p q hp hq i
  exact (hprefix p q hp hq i).trans (by omega)


end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run_oai
