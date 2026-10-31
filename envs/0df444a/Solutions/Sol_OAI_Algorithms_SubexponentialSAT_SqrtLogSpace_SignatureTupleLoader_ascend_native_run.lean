-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:59:33.215181+00:00
-- url     : https://prove2.me/submissions/215e4c73-3965-4b7a-a681-4cc38bc5a5a9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_load_run_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_result_headsize
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_resume_candidate_ready
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_advance_endpoint_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_resume_loaded_storage
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

theorem increment_eval {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (incrementCmd p) (rippleCost true (d.stacks p.counter) + 1)
      d (incrementResult p d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram true) p.register (stackPorts p) d
    p.register.injective (stackPorts p).injective
    (ripple_local_trace true (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (incrementCmd p) _
    (install p d _ _ _ _ []) (incrementResult p d) at h
  rw [← hs, install_self] at h
  exact h

/-- Every off-counter caller stack is preserved, including cleared scratch. -/
theorem incrementResult_stacks {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    (incrementResult p d).stacks =
      Function.update d.stacks p.counter (ripple true (d.stacks p.counter)) := by
  funext i
  by_cases hc : i = p.counter
  · subst i
    simp
  · by_cases hi : i = p.scratch
    · subst i
      simp [hc, hs]
    · rw [Function.update_of_ne hc]
      exact install_other_stack p d _ _ _ _ _ i hc hi

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

/-- Resume consumes one suspended frame and exactly restores its payload. -/
theorem popFrame_trace (word frames : List Bool) (v present : Bool) :
    Trace ParserProgram.frameProgram (6 * word.length + 4)
      (ParserProgram.cfg (some 0) v present (Encoding.frame word.reverse ++ frames) [])
      (ParserProgram.cfg none false true frames word) := by
  simpa using ParserProgram.frame_trace word.reverse frames [] v present

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

theorem advance_eval (a : State 40 896)
    (hcs : a.stacks candidatePorts.scratch = [])
    (hrs : a.stacks remainingPorts.scratch = []) :
    Eval advanceCommand (advanceTime a) a (advanceState a) := by
  have hs : (Counters.incrementResult candidatePorts a).stacks remainingPorts.scratch = [] := by
    rw [Counters.incrementResult_stacks candidatePorts a hcs]
    rw [Function.update_of_ne (by decide : remainingPorts.scratch ≠ candidatePorts.counter)]
    exact hrs
  have he : (Counters.incrementResult candidatePorts a).stacks remainingPorts.counter =
      a.stacks remainingPorts.counter := by
    rw [Counters.incrementResult_stacks candidatePorts a hcs]
    exact Function.update_of_ne (by decide : remainingPorts.counter ≠ candidatePorts.counter) _ _
  have ht := Eval.seq (Counters.increment_eval candidatePorts a hcs)
    (Eval.seq (CounterForPrograms.advance_eval remainingPorts _ hs)
      (Eval.base (StructuredProgram.Eval.atom
        (.copy controllerPorts.available (remainingPorts.register 2)) _)))
  simpa only [advanceCommand, advanceTime, advanceState, CounterForPrograms.advanceCost, he]
    using ht

/-- The per-candidate overhead is polynomial in word widths, although the
represented remaining count can be exponential. -/
theorem advanceTime_le (a : State 40 896)
    (hr : 0 < CounterPrograms.value (a.stacks remainingPorts.counter)) :
    advanceTime a ≤ 8 * (a.stacks candidatePorts.counter).length +
      16 * (a.stacks remainingPorts.counter).length + 24 := by
  have hi := CounterPrograms.rippleCost_le true (a.stacks candidatePorts.counter)
  have hd := CounterForPrograms.advanceCost_le remainingPorts a hr
  unfold advanceTime
  omega

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

theorem popWord_eval (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896)
    (word tail : List Bool) (hs : a.stacks src = Encoding.frame word.reverse ++ tail)
    (hd : a.stacks dst = []) :
    Eval (popWordCommand src dst h) (6 * word.length + 4) a
      (popWordState src dst h a word tail) := by
  have ht := eval_call_lifted ParserProgram.frameProgram frameRegisters (wordPorts src dst h) a
    frameRegisters.injective (wordPorts src dst h).injective
    (a := frameState (a.regs 0) (a.regs 1) (Encoding.frame word.reverse ++ tail) [])
    (b := frameState false true tail word)
    (popFrame_trace word tail (a.regs 0) (a.regs 1))
  rw [← hs, ← hd, word_embed_self] at ht
  exact ht

theorem popWordState_src (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) :
    (popWordState src dst h a word tail).stacks src = tail :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 0

theorem popWordState_dst (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) :
    (popWordState src dst h a word tail).stacks dst = word :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 1

theorem popWordState_outside (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (popWordState src dst h a word tail).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

theorem restoreCursor_eval (a : State 40 896) (candidate remaining frames : List Bool)
    (hs : a.stacks (tupleStacks 0) = Encoding.frame remaining.reverse ++
      Encoding.frame candidate.reverse ++ frames)
    (hc : a.stacks (tupleStacks 2) = []) (hr : a.stacks (tupleStacks 7) = []) :
    Eval restoreCursorCommand (6 * remaining.length + 6 * candidate.length + 8) a
      (restoreCursorState a candidate remaining frames) := by
  have hs' : a.stacks (tupleStacks 0) = Encoding.frame remaining.reverse ++
      (Encoding.frame candidate.reverse ++ frames) := by simpa only [List.append_assoc] using hs
  have h1 := popWord_eval (tupleStacks 0) (tupleStacks 7) (by decide) a remaining
    (Encoding.frame candidate.reverse ++ frames) hs' hr
  have h2 := popWord_eval (tupleStacks 0) (tupleStacks 2) (by decide)
    (popWordState (tupleStacks 0) (tupleStacks 7) (by decide) a remaining
      (Encoding.frame candidate.reverse ++ frames)) candidate frames
    (popWordState_src _ _ _ _ _ _) (by
      rw [popWordState_outside _ _ _ _ _ _ _ (by decide) (by decide)]
      exact hc)
  have ht := Eval.seq h1 h2
  change Eval restoreCursorCommand _ a (restoreCursorState a candidate remaining frames) at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem restoreCursorState_words (a : State 40 896) (candidate remaining frames : List Bool) :
    (restoreCursorState a candidate remaining frames).stacks (tupleStacks 2) = candidate ∧
      (restoreCursorState a candidate remaining frames).stacks (tupleStacks 7) = remaining ∧
      (restoreCursorState a candidate remaining frames).stacks (tupleStacks 0) = frames := by
  constructor
  · exact popWordState_dst _ _ _ _ _ _
  constructor
  · unfold restoreCursorState
    rw [popWordState_outside _ _ _ _ _ _ _ (by decide) (by decide), popWordState_dst]
  · exact popWordState_src _ _ _ _ _ _

theorem ascendLevel_eval (a : State 40 896) :
    Eval ascendLevelCommand 4 a (ascendLevelState a) :=
  .base (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))))

theorem ascendLevelState_words (a : State 40 896) (remaining address : ℕ)
    (hr : a.stacks (tupleStacks 6) = List.replicate remaining true)
    (ha : a.stacks (tupleStacks 9) = List.replicate (address + 1) true) :
    (ascendLevelState a).stacks (tupleStacks 6) = List.replicate (remaining + 1) true ∧
      (ascendLevelState a).stacks (tupleStacks 9) = List.replicate address true ∧
      (ascendLevelState a).regs controllerPorts.leaf = false := by
  have h69 : tupleStacks 6 ≠ tupleStacks 9 := by decide
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
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

theorem dropRepresentative_eval (a : State 40 896) (word reps : List Bool)
    (hs : a.stacks (tupleStacks 1) = Encoding.frame word.reverse ++ reps)
    (he : a.stacks (tupleStacks 4) = []) :
    Eval dropRepresentativeCommand (8 * word.length + 7) a
      (dropRepresentativeState a word reps) := by
  have ht := Eval.seq (popWord_eval (tupleStacks 1) (tupleStacks 4) (by decide) a word reps hs he)
    (clearWord_eval (tupleStacks 4) _)
  rw [popWordState_dst] at ht
  change Eval dropRepresentativeCommand _ a (dropRepresentativeState a word reps) at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem dropRepresentativeState_stacks (a : State 40 896) (word reps : List Bool) :
    (dropRepresentativeState a word reps).stacks (tupleStacks 1) = reps ∧
      (dropRepresentativeState a word reps).stacks (tupleStacks 4) = [] := by
  constructor
  · change Function.update
      (popWordState (tupleStacks 1) (tupleStacks 4) (by decide) a word reps).stacks
      (tupleStacks 4) [] (tupleStacks 1) = reps
    rw [Function.update_of_ne (by decide : tupleStacks 1 ≠ tupleStacks 4)]
    exact popWordState_src _ _ _ _ _ _
  · simp [dropRepresentativeState, clearState]

theorem testParent_eval (a : State 40 896) :
    Eval testParentCommand 1 a (testParentState a) := .base (.atom _ _)

theorem testParentState_flag (a : State 40 896) :
    (testParentState a).regs controllerPorts.active =
      decide (a.stacks (tupleStacks 0) ≠ []) := by
  cases hs : a.stacks (tupleStacks 0) <;>
    simp [testParentState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hs]

theorem popWordState_register_frame (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool)
    (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (popWordState src dst h a word tail).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact h0 hj.symm
  · exact h1 hj.symm

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

/-- Popping an ancestor restores precisely the previous dependent prefix. -/
theorem representativeFrames_pop (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) :
    representativeFrames h key (depth + 1) ancestors =
      Encoding.frame (fixedBits (h depth) (ancestors (Fin.last depth)).val.val).reverse ++
        representativeFrames h key depth (Fin.init ancestors) := by
  simpa only [Fin.snoc_init_self] using
    representativeFrames_snoc h key depth (Fin.init ancestors) (ancestors (Fin.last depth))

theorem cursorFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      cursorFrame (h depth) rep.val.val ++ cursorFrames h key depth ancestors := by
  simp only [cursorFrames, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatten_cons]
  rfl

theorem cursorFrames_pop (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) :
    cursorFrames h key (depth + 1) ancestors =
      cursorFrame (h depth) (ancestors (Fin.last depth)).val.val ++
        cursorFrames h key depth (Fin.init ancestors) := by
  simpa only [Fin.snoc_init_self] using
    cursorFrames_snoc h key depth (Fin.init ancestors) (ancestors (Fin.last depth))

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

private theorem drop_outside (a : StructuredProgram.State 40 896) (word reps : List Bool)
    (i : Fin 896) (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (dropRepresentativeState a word reps).stacks i = a.stacks i := by
  change Function.update (popWordState _ _ _ a word reps).stacks (tupleStacks 4) [] i = _
  rw [Function.update_of_ne hp, popWordState_outside _ _ _ _ _ _ _ hr hp]

private theorem restore_outside (a : StructuredProgram.State 40 896)
    (candidate remaining frames : List Bool) (i : Fin 896)
    (hf : i ≠ tupleStacks 0) (hc : i ≠ tupleStacks 2) (hr : i ≠ tupleStacks 7) :
    (restoreCursorState a candidate remaining frames).stacks i = a.stacks i := by
  unfold restoreCursorState
  rw [popWordState_outside _ _ _ _ _ _ _ hf hc,
    popWordState_outside _ _ _ _ _ _ _ hf hr]

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- Dropping the just-finished representative and restoring the two saved
cursor words gives exactly `Fin.init`, before the paid parent increment. -/
theorem returnFrames_state (depth : ℕ) (ancestors : Prefix (Representatives key) (depth + 1))
    (a : StructuredProgram.State 40 896) :
    let word := fixedBits (h depth) (ancestors (Fin.last depth)).val.val
    let remaining := fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val)
    let reps := representativeFrames h key depth (Fin.init ancestors)
    let frames := cursorFrames h key depth (Fin.init ancestors)
    let b := restoreCursorState (dropRepresentativeState a word reps) word remaining frames
    b.stacks (tupleStacks 0) = frames ∧ b.stacks (tupleStacks 1) = reps ∧
    b.stacks (tupleStacks 2) = word ∧ b.stacks (tupleStacks 7) = remaining ∧
    b.stacks (tupleStacks 4) = [] := by
  dsimp only
  have hs := restoreCursorState_words
    (dropRepresentativeState a
      (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
      (representativeFrames h key depth (Fin.init ancestors)))
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val))
    (cursorFrames h key depth (Fin.init ancestors))
  refine ⟨hs.2.2, ?_, hs.1, hs.2.1, ?_⟩
  · rw [restore_outside _ _ _ _ (tupleStacks 1) (by decide) (by decide) (by decide)]
    exact (dropRepresentativeState_stacks _ _ _).1
  · rw [restore_outside _ _ _ _ (tupleStacks 4) (by decide) (by decide) (by decide)]
    exact (dropRepresentativeState_stacks _ _ _).2

theorem returnFrames_eval (depth : ℕ) (ancestors : Prefix (Representatives key) (depth + 1))
    (a : StructuredProgram.State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors)
    (hr : a.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) ancestors)
    (hc : a.stacks (tupleStacks 2) = []) (hn : a.stacks (tupleStacks 7) = [])
    (hp : a.stacks (tupleStacks 4) = []) :
    let word := fixedBits (h depth) (ancestors (Fin.last depth)).val.val
    let remaining := fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val)
    let reps := representativeFrames h key depth (Fin.init ancestors)
    let frames := cursorFrames h key depth (Fin.init ancestors)
    Eval (.seq dropRepresentativeCommand restoreCursorCommand) (20 * h depth + 21) a
      (restoreCursorState (dropRepresentativeState a word reps) word remaining frames) := by
  dsimp only
  have hd := dropRepresentative_eval a
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (representativeFrames h key depth (Fin.init ancestors))
    (hr.trans (representativeFrames_pop h key depth ancestors)) hp
  have hs := restoreCursor_eval (dropRepresentativeState a
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (representativeFrames h key depth (Fin.init ancestors)))
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val))
    (cursorFrames h key depth (Fin.init ancestors)) (by
      rw [drop_outside _ _ _ (tupleStacks 0) (by decide) (by decide), hf,
        cursorFrames_pop, cursorFrame])
    (by rw [drop_outside _ _ _ (tupleStacks 2) (by decide) (by decide), hc])
    (by rw [drop_outside _ _ _ (tupleStacks 7) (by decide) (by decide), hn])
  have he := hd.seq hs
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

/-- No physical tape outside the two counters and their decrement scratch is
changed by advancement. The increment scratch is restored as well. -/
theorem advanceState_outside (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = []) (i : Fin 896)
    (hc : i ≠ candidatePorts.counter) (hr : i ≠ remainingPorts.counter)
    (ht : i ≠ remainingPorts.scratch) :
    (advanceState a).stacks i = a.stacks i := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks i = a.stacks i
  rw [← CounterForPrograms.nextState_outside remainingPorts _ i hr ht]
  rw [Counters.incrementResult_stacks candidatePorts a hs, Function.update_of_ne hc]

theorem advanceCandidate_eval (a : State 40 896)
    (hc : a.stacks candidatePorts.scratch = [])
    (hr : a.stacks remainingPorts.scratch = []) :
    Eval advanceCandidateCommand
      (advanceTime a + 2 * (a.stacks (tupleStacks 3)).length + 3) a
      (advanceCandidateState a) := by
  have he := (advance_eval a hc hr).seq (clearWord_eval (tupleStacks 3) (advanceState a))
  rw [advanceState_outside a hc (tupleStacks 3) (by decide) (by decide) (by decide)] at he
  simpa only [advanceCandidateCommand, advanceCandidateState, Nat.add_assoc] using he

theorem CursorWords.remaining_value {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - c := by
  rw [hw.remaining]
  apply ExecCNFTupleEnumeration.fixedBits_value
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega


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

theorem seq_reassociate {first second third : Cmd 40 896} {n : ℕ} {a b : State 40 896}
    (he : Eval (.seq (.seq first second) third) n a b) :
    Eval (.seq first (.seq second third)) n a b := by
  cases he with
  | seq hab hc =>
    cases hab with
    | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)

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


/-- The presence test does not change any stack, and cleanup leaves both
persistent prefix banks intact. -/
theorem checkedReturnState_stack (a : State 40 896) (i : Fin 896) :
    (rootAscendState a).stacks i = if i ∈ currentHeadPorts then [] else a.stacks i :=
  clearWordsState_stacks currentHeadPorts a i

section ParentReturn

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem cursorFrames_nonempty (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) :
    cursorFrames h key (depth + 1) ancestors ≠ [] := by
  intro he
  have hl := congrArg List.length he
  rw [cursorFrames_pop, List.length_append, cursorFrame_length, List.length_nil] at hl
  omega

theorem checkedReturnState_active (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors) :
    (rootAscendState a).regs controllerPorts.active = true := by
  rw [rootAscendState, testParentState_flag, clearWordsState_stacks,
    ite_eq_right (by decide), hf]
  exact decide_eq_true (cursorFrames_nonempty h key depth ancestors)

/-- Restore the attained parent's saved bounded candidate and fuel without
rescanning any earlier candidate. The matrix reload follows this prefix. -/
theorem parent_return_prefix_eval (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors)
    (hr : a.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) ancestors) :
    Eval (.seq dropRepresentativeCommand (.seq restoreCursorCommand ascendLevelCommand))
      (20 * h depth + 25) (rootAscendState a) (parentReturnState h key depth ancestors a) := by
  have he := returnFrames_eval h key depth ancestors (rootAscendState a)
    (by rw [checkedReturnState_stack, ite_eq_right (by decide), hf])
    (by rw [checkedReturnState_stack, ite_eq_right (by decide), hr])
    (by rw [checkedReturnState_stack, ite_eq_left (by decide)])
    (by rw [checkedReturnState_stack, ite_eq_left (by decide)])
    (by rw [checkedReturnState_stack, ite_eq_left (by decide)])
  have hall := seq_reassociate (he.seq (ascendLevel_eval (parentWordsState h key depth ancestors a)))
  change Eval _ _ (rootAscendState a) (parentReturnState h key depth ancestors a) at hall
  convert hall using 1
  all_goals try with_reducible_and_instances rfl

theorem parentWordsState_fields (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) :
    (parentWordsState h key depth ancestors a).stacks (tupleStacks 0) =
        cursorFrames h key depth (Fin.init ancestors) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 1) =
        representativeFrames h key depth (Fin.init ancestors) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 2) =
        ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 7) =
        ExecCNFTupleEnumeration.fixedBits (h depth + 1)
          (2 ^ h depth - (ancestors (Fin.last depth)).val.val) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 4) = [] :=
  returnFrames_state h key depth ancestors (rootAscendState a)


theorem parentWordsState_outside (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (i : Fin 896)
    (h0 : i ≠ tupleStacks 0) (h1 : i ≠ tupleStacks 1) (h2 : i ≠ tupleStacks 2)
    (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (parentWordsState h key depth ancestors a).stacks i = (rootAscendState a).stacks i := by
  unfold parentWordsState restoreCursorState
  rw [popWordState_outside _ _ _ _ _ _ _ h0 h2,
    popWordState_outside _ _ _ _ _ _ _ h0 h7]
  change Function.update (popWordState _ _ _ _ _ _).stacks (tupleStacks 4) [] i = _
  rw [Function.update_of_ne h4, popWordState_outside _ _ _ _ _ _ _ h1 h4]

theorem parentWordsState_register (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (parentWordsState h key depth ancestors a).regs j = (rootAscendState a).regs j := by
  unfold parentWordsState restoreCursorState
  rw [popWordState_register_frame _ _ _ _ _ _ j h0 h1,
    popWordState_register_frame _ _ _ _ _ _ j h0 h1]
  change readRegs (popWordState _ _ _ _ _ _).regs 0 1 none j = _
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1,
    popWordState_register_frame _ _ _ _ _ _ j h0 h1]

theorem ascendLevelState_outside (a : State 40 896) (i : Fin 896)
    (h6 : i ≠ tupleStacks 6) (h9 : i ≠ tupleStacks 9) :
    (ascendLevelState a).stacks i = a.stacks i := by
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h6, h9]

theorem ascendLevelState_active (a : State 40 896) :
    (ascendLevelState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    controllerPorts]

/-- The parent address and unary remaining-head word are reconstructed by
one paid ascent; no saved matrix or whole assignment table is retained. -/
theorem parent_return_ancestor_storage (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (ha : AncestorStorage h key levels base (depth + 1) ancestors a) :
    AncestorStorage h key levels base depth (Fin.init ancestors)
      (parentReturnState h key depth ancestors a) := by
  have hf := parentWordsState_fields h key depth ancestors a
  have hh : (parentWordsState h key depth ancestors a).stacks (tupleStacks 6) =
      List.replicate (levels - (depth + 1)) true := by
    rw [parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_right (by decide)]
    exact ha.heads
  have hz : (parentWordsState h key depth ancestors a).stacks (tupleStacks 9) =
      List.replicate (base + depth + 1) true := by
    rw [parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_right (by decide), ha.address]
    simp [Nat.add_assoc]
  have hl := ascendLevelState_words (parentWordsState h key depth ancestors a)
    (levels - (depth + 1)) (base + depth) hh hz
  refine ⟨by have := ha.depth_le; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [parentReturnState, hl.1]
    have hd := ha.depth_le
    congr 1
    omega
  · exact hl.2.1
  · rw [parentReturnState, ascendLevelState_active,
      parentWordsState_register _ _ _ _ _ _ (by decide) (by decide)]
    exact checkedReturnState_active h key depth ancestors a ha.cursors

theorem parent_return_cursor (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) :
    CursorWords (parentReturnState h key depth ancestors a) (h depth)
      (ancestors (Fin.last depth)).val.val := by
  have hf := parentWordsState_fields h key depth ancestors a
  have hcan : (parentReturnState h key depth ancestors a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val := by
    rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.2.1
  have hrem : (parentReturnState h key depth ancestors a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h depth + 1)
        (2 ^ h depth - (ancestors (Fin.last depth)).val.val) := by
    rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.2.2.1
  refine ⟨(ancestors (Fin.last depth)).val.isLt.le, ?_, ?_, fun _ => hcan, hrem, ?_, ?_⟩
  · rw [hcan]
    exact ExecCNFTupleEnumeration.fixedBits_value _ _ (ancestors (Fin.last depth)).val.isLt
  · rw [hcan, ExecCNFTupleEnumeration.fixedBits_length]
    omega
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide),
      parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_left (by decide)]
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide),
      parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_left (by decide)]

end ParentReturn


theorem copyPredecessor_cursor (a : State 40 896) (h candidate : ℕ)
    (hw : CursorWords a h candidate) :
    CursorWords (copyState 651 (tupleStacks 8) a) h candidate := by
  have hf (i : Fin 896) (hi : i ≠ tupleStacks 8) :
      (copyState 651 (tupleStacks 8) a).stacks i = a.stacks i := by
    simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne hi]
  refine ⟨hw.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf _ (by decide)]; exact hw.value
  · rw [hf _ (by decide)]; exact hw.width
  · intro hc; rw [hf _ (by decide)]; exact hw.exact hc
  · rw [hf _ (by decide)]; exact hw.remaining
  · rw [hf _ (by decide)]; exact hw.incrementScratch
  · rw [hf _ (by decide)]; exact hw.decrementScratch

theorem resume_loaded_run_space (a : State 40 896) (h candidate F : ℕ)
    (hw : CursorWords a h candidate) (hc : candidate < 2 ^ h)
    (hwidth : a.stacks 651 = List.replicate h false)
    (hz : a.stacks (tupleStacks 8) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hcursor : h + 1 ≤ F) :
    ∃ n,
      Eval (.seq resetPredecessorCommand advanceCandidateCommand) n a
        (advanceCandidateState (copyState 651 (tupleStacks 8) a)) ∧
      (∀ i, ((advanceCandidateState (copyState 651 (tupleStacks 8) a)).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (.seq resetPredecessorCommand advanceCandidateCommand) 0 0) prefixSteps
          (a.withPC (some (compiled (.seq resetPredecessorCommand advanceCandidateCommand) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
      n + 1 ≤ 33 * F + 49 := by
  let b := copyState 651 (tupleStacks 8) a
  have hwords := copyPredecessor_cursor a h candidate hw
  have hcopy := copyWord_eval 651 (tupleStacks 8) (tupleStacks 5)
    (by decide) (by decide) (by decide) a hw.decrementScratch
  rw [hwidth, List.length_replicate] at hcopy
  have hadv := advanceCandidate_eval b hwords.incrementScratch hwords.decrementScratch
  have he : Eval (.seq resetPredecessorCommand advanceCandidateCommand)
      (7 * h + 5 + (advanceTime b + 2 * (b.stacks (tupleStacks 3)).length + 3)) a
      (advanceCandidateState b) := hcopy.seq hadv
  have hb : ∀ i, (b.stacks i).length ≤ F := by
    intro i
    by_cases hi : i = tupleStacks 8
    · subst i
      simp only [b, copyState, StackRoutines.copyStacks, Function.update_self,
        hwidth, hz, List.append_nil, List.length_replicate]
      omega
    · simpa only [b, copyState, StackRoutines.copyStacks, Function.update_of_ne hi] using hframe i
  have hpos : 0 < CounterPrograms.value (b.stacks remainingPorts.counter) := by
    rw [hwords.remaining_value]
    omega
  have htime := advanceTime_le b hpos
  rw [hwords.exact hc, hwords.remaining] at htime
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at htime
  have hk := hb (tupleStacks 3)
  have hn : 7 * h + 5 + (advanceTime b + 2 * (b.stacks (tupleStacks 3)).length + 3) + 1 ≤
      33 * F + 49 := by omega
  refine ⟨_, he, advance_endpoint_bound b h candidate F hwords hc hb hcursor, ?_, hn⟩
  have hs := StructuredSpace.local_stack_bound
    (compiled (.seq resetPredecessorCommand advanceCandidateCommand) 0 0)
    (a := a.withPC (some (compiled (.seq resetPredecessorCommand advanceCandidateCommand) 0 0).entry))
    (steps := 33 * F + 49) (StreamResources.dataBits_le_mul _ hframe)
  intro p q hp hq i
  exact (hs p q (by omega) hq i).trans (by omega)

theorem parent_return_current_empty (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (i : Fin 896) (hi : i ∈ currentHeadPorts)
    (h2 : i ≠ tupleStacks 2) (h7 : i ≠ tupleStacks 7) :
    (parentReturnState h key depth ancestors a).stacks i = [] := by
  have hports : i ≠ tupleStacks 0 ∧ i ≠ tupleStacks 1 ∧
      i ≠ tupleStacks 6 ∧ i ≠ tupleStacks 9 := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [parentReturnState, ascendLevelState_outside _ _ hports.2.2.1 hports.2.2.2]
  by_cases h4 : i = tupleStacks 4
  · subst i
    exact (parentWordsState_fields h key depth ancestors a).2.2.2.2
  · rw [parentWordsState_outside _ _ _ _ _ _ hports.1 hports.2.1 h2 h4 h7,
      checkedReturnState_stack, ite_eq_left hi]

theorem parentReturnState_outside_tuple (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) :
    (parentReturnState h key depth ancestors a).stacks i = a.stacks i := by
  have hc : i ∉ currentHeadPorts := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨hi 2, hi 3, hi 4, hi 5, hi 7, hi 8, hi 10, hi 11⟩
  rw [parentReturnState, ascendLevelState_outside _ _ (hi 6) (hi 9),
    parentWordsState_outside _ _ _ _ _ _ (hi 0) (hi 1) (hi 2) (hi 4) (hi 7),
    checkedReturnState_stack, ite_eq_right hc]

/-- Restoring a suspended parent again fits the same global frame and word
cap before its matrix is reloaded. No transient cost is accumulated. -/
theorem parent_return_endpoint_bound (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base depth hmax F : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (ha : AncestorStorage h key levels base (depth + 1) ancestors a)
    (hh : ∀ d < levels, h d ≤ hmax)
    (hcap : 6 * levels * (hmax + 1) + (base + levels) + (hmax + 1) ≤ F)
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∀ i, ((parentReturnState h key depth ancestors a).stacks i).length ≤ F := by
  have hb := parent_return_ancestor_storage h key levels base depth ancestors a ha
  have hw := parent_return_cursor h key depth ancestors a
  have hf := hb.frame_bound h key hmax hh
  have hd : depth < levels := by have := ha.depth_le; omega
  have hwidth := hh depth hd
  have hz (i : Fin 896) (hi : i ∈ currentHeadPorts)
      (h2 : i ≠ tupleStacks 2) (h7 : i ≠ tupleStacks 7) :
      (parentReturnState h key depth ancestors a).stacks i = [] :=
    parent_return_current_empty h key depth ancestors a i hi h2 h7
  intro i
  by_cases hi : ∃ j : Fin 12, i = tupleStacks j
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 0)).length ≤ F
      omega
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 1)).length ≤ F
      omega
    · change ((parentReturnState h key depth ancestors a).stacks candidatePorts.counter).length ≤ F
      have := hw.width
      omega
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 3)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 4)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 5)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 6)).length ≤ F
      rw [hb.heads, List.length_replicate]
      omega
    · change ((parentReturnState h key depth ancestors a).stacks remainingPorts.counter).length ≤ F
      rw [hw.remaining, ExecCNFTupleEnumeration.fixedBits_length]
      omega
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 8)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 9)).length ≤ F
      rw [hb.address, List.length_replicate]
      omega
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 10)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
    · change ((parentReturnState h key depth ancestors a).stacks (tupleStacks 11)).length ≤ F
      rw [hz _ (by decide) (by decide) (by decide)]
      simp
  · rw [parentReturnState_outside_tuple h key depth ancestors a i (fun j hj => hi ⟨j, hj⟩)]
    exact hframe i

/-- A nonroot return composes the actual bounded frame restoration, actual
matrix reload evaluation, and one cursor advance. Its storage estimate uses
only this polynomial reload time, never the preceding traversal length. -/
theorem ascend_loaded_run_space (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (loadHead : Cmd 40 896)
    (depth F loadSteps : ℕ) (ancestors : Prefix (Representatives key) (depth + 1))
    (a loaded : State 40 896)
    (hframes : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors)
    (hreps : a.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) ancestors)
    (hload : Eval loadHead loadSteps (parentReturnState h key depth ancestors a) loaded)
    (hwords : CursorWords loaded (h depth) (ancestors (Fin.last depth)).val.val)
    (hwidth : loaded.stacks 651 = List.replicate (h depth) false)
    (hz : loaded.stacks (tupleStacks 8) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F)
    (hloaded : ∀ i, (loaded.stacks i).length ≤ F) (hcursor : h depth + 1 ≤ F) :
    ∃ n,
      Eval (ascendWith loadHead) n a (advanceCandidateState (copyState 651 (tupleStacks 8) loaded)) ∧
      (∀ i, ((advanceCandidateState (copyState 651 (tupleStacks 8) loaded)).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (ascendWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1) + loadSteps) ∧
      n + 1 ≤ loadSteps + 69 * F + 100 := by
  obtain ⟨nt, ht, hend, _, hnt⟩ := resume_loaded_run_space loaded (h depth)
    (ancestors (Fin.last depth)).val.val F hwords (ancestors (Fin.last depth)).val.isLt
    hwidth hz hloaded hcursor
  have hp := parent_return_prefix_eval h key depth ancestors a hframes hreps
  have hresume : Eval (resumeParentWith loadHead) (20 * h depth + 25 + loadSteps + nt)
      (rootAscendState a) (advanceCandidateState (copyState 651 (tupleStacks 8) loaded)) := by
    generalize hcost : 20 * h depth + 25 = frameSteps at hp
    cases hp with
    | seq hdrop hrest =>
      cases hrest with
      | seq hrestore hascend =>
        have he := hdrop.seq (hrestore.seq (hascend.seq (hload.seq ht)))
        change Eval (resumeParentWith loadHead) _ (rootAscendState a) _ at he
        convert he using 1
        all_goals try with_reducible_and_instances rfl
        omega
  have hb : Eval (.ite controllerPorts.active (resumeParentWith loadHead) (.base .skip))
      (20 * h depth + 25 + loadSteps + nt + 1) (rootAscendState a)
      (advanceCandidateState (copyState 651 (tupleStacks 8) loaded)) :=
    .ite_true (checkedReturnState_active h key depth ancestors a hframes) hresume
  have hall := (clearWords_eval currentHeadPorts a).seq
    ((testParent_eval (clearWordsState currentHeadPorts a)).seq hb)
  change Eval (ascendWith loadHead) _ a _ at hall
  have hc := clearWordsTime_le_on currentHeadPorts a F (fun i _ => hframe i)
  change clearWordsTime currentHeadPorts a ≤ 8 * (2 * F + 3) at hc
  have hn : clearWordsTime currentHeadPorts a +
      (1 + (20 * h depth + 25 + loadSteps + nt + 1)) + 1 ≤ loadSteps + 69 * F + 100 := by omega
  refine ⟨_, hall, hend, ?_, hn⟩
  have hs := StructuredSpace.local_stack_bound (compiled (ascendWith loadHead) 0 0)
    (a := a.withPC (some (compiled (ascendWith loadHead) 0 0).entry))
    (steps := loadSteps + 69 * F + 100) (StreamResources.dataBits_le_mul _ hframe)
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


private theorem low_outside_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  have := i.isLt
  omega

theorem parent_return_masters (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth+1)) (a : State 40 896) (base : Data)
    (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (parentReturnState h key depth ancestors a)) := by
  constructor
  intro i hi
  exact (parentReturnState_outside_tuple h key depth ancestors a
    (SignatureHeadLoader.lowStacks i) (low_outside_tuple i)).trans (hm.stored i hi)

/-- Reloading changes the current matrix, while the restored bounded
candidate and remaining-assignment words retain their exact values. -/
theorem result_cursor_words (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (h c : ℕ) (hw : CursorWords frame h c) :
    CursorWords (result s z frame rp rm rs raw shifted) h c := by
  have hc := result_high_frame s z frame rp rm rs raw shifted
    candidatePorts.counter (by decide) (by decide)
  have hr := result_high_frame s z frame rp rm rs raw shifted
    remainingPorts.counter (by decide) (by decide)
  have hs := result_high_frame s z frame rp rm rs raw shifted
    remainingPorts.scratch (by decide) (by decide)
  refine ⟨hw.range,?_,?_,?_,?_,?_,?_⟩
  · rw [hc]; exact hw.value
  · rw [hc]; exact hw.width
  · intro hn; rw [hc]; exact hw.exact hn
  · rw [hr]; exact hw.remaining
  · exact result_raw_empty ..
  · rw [hs]; exact hw.decrementScratch


/-- Returning to a parent uses the actual native reload and advances its
restored cursor once. No earlier predecessor scan is repeated. -/
theorem ascend_native_run_oai (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) (depth.val+1))
    (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
    (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hanc : AncestorStorage h key levels base (depth.val+1) ancestors a)
    (F L hmax : ℕ) (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
    (hh : ∀ d<levels,h d≤hmax)
    (hcap : 6*levels*(hmax+1)+(base+levels)+(hmax+1)≤F)
    (hsize : (selectedHeads s.n s.rows s.low (base+depth.val)).length=h depth.val) :
    ∃ rp rm rs raw shifted total,
      let loaded := result s (base+depth.val) (parentReturnState h key depth.val ancestors a)
        rp rm rs raw shifted
      let finish := advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) loaded)
      Eval (ascendWith loadHead) total a finish ∧
      total+1 ≤ runEnvelope B F+69*F+100 ∧ WordBound F finish ∧
      ScanStorage h key levels base depth (Fin.init ancestors)
        ((ancestors (Fin.last depth.val)).val.val+1) finish ∧
      (∀ hn : (ancestors (Fin.last depth.val)).val.val+1<2^h depth.val,
        CandidateReady finish (a.stacks 141) shifted (h depth.val) ⟨_,hn⟩) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low (base+depth.val)) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (ascendWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F := by
  let b := parentReturnState h key depth.val ancestors a
  have hb := parent_return_endpoint_bound h key levels base depth.val hmax F ancestors a hanc hh hcap hf
  have hbm := parent_return_masters h key depth.val ancestors a _ hm
  have hbanc := parent_return_ancestor_storage h key levels base depth.val ancestors a hanc
  have hbw := parent_return_cursor h key depth.val ancestors a
  have hbW : b.stacks 141=a.stacks 141 :=
    parentReturnState_outside_tuple h key depth.val ancestors a 141 (low_outside_tuple 141)
  have hblank (i : Fin 896) (hi : i∈currentHeadPorts)
      (h2 : i≠tupleStacks 2) (h7 : i≠tupleStacks 7) : b.stacks i=[] :=
    parent_return_current_empty h key depth.val ancestors a i hi h2 h7
  obtain ⟨rp,rm,rs,raw,shifted,loadSteps,hload,hloadTime,hloaded,hraw,hshift,_⟩ :=
    load_run_polynomial s source ha B hB hrows ra rd rc words hw b hbm (base+depth.val) F L
      hbanc.address hb (by simpa only [hbW] using hW) hout
  let loaded := result s (base+depth.val) b rp rm rs raw shifted
  have hhigh (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
      loaded.stacks i=b.stacks i := result_high_frame s (base+depth.val) b rp rm rs raw shifted i hi hne
  have hloadedWords := result_cursor_words s (base+depth.val) b rp rm rs raw shifted _ _ hbw
  have hwidth : loaded.stacks 651=List.replicate (h depth.val) false := by
    rw [result_headsize,hsize]
  have hpred : loaded.stacks (tupleStacks 8)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide) (by decide) (by decide))
  have hpayload : loaded.stacks (tupleStacks 4)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide) (by decide) (by decide))
  have hsaved : loaded.stacks (tupleStacks 3)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide) (by decide) (by decide))
  have hcursor : h depth.val+1≤F := by have := hh depth.val depth.isLt; omega
  obtain ⟨total,he,hend,hprefix,ht⟩ := ascend_loaded_run_space h key loadHead depth.val F loadSteps
    ancestors a loaded hanc.cursors hanc.representatives hload hloadedWords hwidth hpred hf hloaded hcursor
  have hl : loaded.regs controllerPorts.leaf=false := by
    rw [result_register_frame s (base+depth.val) b rp rm rs raw shifted controllerPorts.leaf (by decide)]
    rfl
  have hscan := resume_loaded_storage h key levels base depth (Fin.init ancestors)
    (ancestors (Fin.last depth.val)).val.val loaded
    (result_ancestor_storage h key levels base depth.val (Fin.init ancestors)
      s (base+depth.val) b rp rm rs raw shifted hbanc)
    hloadedWords (ancestors (Fin.last depth.val)).val.isLt hl hwidth hpayload hpred
  rw [hbW] at hshift
  refine ⟨rp,rm,rs,raw,shifted,total,he,by omega,hend,hscan,?_,hraw,hshift,?_⟩
  · intro hn
    apply resume_candidate_ready loaded (a.stacks 141) shifted (h depth.val)
      (ancestors (Fin.last depth.val)).val ⟨_,hn⟩ rfl hloadedWords
    · exact (result_offset s (base+depth.val) b rp rm rs raw shifted).trans hbW
    · exact result_matrix ..
    · exact hwidth
    · exact hsaved
    · exact hpred
    · exact result_rescan_scratch s (base+depth.val) b rp rm rs raw shifted
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by omega)


end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run_oai.{u_1}
