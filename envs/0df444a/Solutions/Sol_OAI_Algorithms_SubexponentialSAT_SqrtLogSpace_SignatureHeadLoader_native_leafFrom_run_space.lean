-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:52:23.300651+00:00
-- url     : https://prove2.me/submissions/84ece3ab-3144-4517-8eb9-96a469ffa597

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_Bounds_prepareHead_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_Native_initial_contract
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_prepareHead_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_raw_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_shift_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramCompatibility
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact serialization and state projection at the all-row bucket boundary. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem ids_eq_indices (js : List ℕ) : ids js=HeadScatterProgram.indices js := rfl

theorem matrixRel_dimensions {Rel : ℕ → ℕ → Pair → Prop} {B D : ℕ} {js : List ℕ}
    {rows : List (List Pair)} (h : MatrixRel Rel B D js rows) :
    rows.length=D ∧ ∀ row ∈ rows, row.length=js.length := by
  refine ⟨?_,?_⟩
  · simpa [MatrixRel] using h.length_eq.symm
  · intro row hr
    have aux : ∀ (is : List ℕ) (rs : List (List Pair)),
        List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
          is rs → ∀ row ∈ rs, row.length=js.length := by
      intro is rs hs
      induction hs with
      | nil => simp
      | cons hi ht ih =>
        intro row hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hi.length_eq.symm
        · exact ih row hr
    exact aux _ _ h row hr

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem embedState_wordBound {r s S : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin S) (frame : Data S) (out : State r s) (B : ℕ)
    (hs : Function.Injective stack) (hf : WordBound B frame) (ho : WordBound B out) :
    WordBound B (embedState register stack frame out) := by
  intro i
  by_cases hm : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hm
    rw [embedState_stack register stack frame out hs j]
    exact ho j
  · rw [embedState_stack_frame register stack frame out i hm]
    exact hf i

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

theorem headOutputs_protected : ∀ p ∈ headOutputs,Protected p.2 := by simp [headOutputs,Protected,temporary]

theorem headResult_ids (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (headResult a n rows low W z).stacks 650=
      HeadScatterProgram.indices (HeadIdentifierProgram.chosenIds
        (HeadIdentifierProgram.predicate rows low z) n) := by
  exact returned_word id (by decide) headInputs headOutputs a _ headOutputs_protected
    (by decide) (0,650) (by simp [headOutputs])

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

theorem preparedHead_ids (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (preparedHead a regs n N rows low W z).stacks 650=
      HeadScatterProgram.indices (selectedHeads n rows low z) := by
  rw [preparedHead,factorResult_frame _ _ _ _ _ _ _ (by decide) (by decide),
    scatterResult_frame _ _ _ _ _ (by decide) (by decide),
    countResult_frame _ _ (by decide) (by decide)]
  exact headResult_ids _ _ _ _ _ _

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

theorem matrixEntry_prepared_master (base b : Data) (hf : MasterFrame base b)
    (rp : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (regs : Fin 16 → Bool) (row col pos neg : List Bool) :
    LayoutMatrixProgram.entryState (matrixBase (preparedHead b rp n N rows low W z))
      regs row col pos neg=
    LayoutMatrixProgram.entryState (matrixBase base) regs row col pos neg := by
  have hs (i : Fin 768) (hi : Protected i) (hm : i∈masters)
      (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
      (preparedHead b rp n N rows low W z).stacks i=base.stacks i :=
    (preparedHead_frame b rp n N rows low W z i hi h650 h651 h652 h670 h671).trans
      (hf.stored i hm)
  have h135 := hs 135 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h136 := hs 136 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h640 := hs 640 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h641 := hs 641 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h140 := hs 140 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h642 := hs 642 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h138 := hs 138 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h139 := hs 139 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h130 := hs 130 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h131 := hs 131 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h307 := hs 307 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h132 := hs 132 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  apply congrArg (StructuredProgram.State.mk regs)
  funext i
  have hn (j : Fin 288) (hj : j.val < 25) : LayoutMatrixProgram.bankPort i≠j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [LayoutMatrixProgram.bankPort] at hv
    omega
  simp only [matrixBase, hn 0 (by decide), hn 17 (by decide), hn 18 (by decide),
    hn 23 (by decide), h135, h136, h640, h641, h140, h642, h138, h139, h130,
    h131, h307, h132, ite_false]

theorem entryContract_prepared_master (entry : Cmd 16 256) (base b : Data) (hf : MasterFrame base b)
    (rp : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : LayoutMatrixProgram.EntryContract entry (matrixBase base) Valid Rel T B) :
    LayoutMatrixProgram.EntryContract entry (matrixBase (preparedHead b rp n N rows low W z))
      Valid Rel T B := by
  intro regs j v hv
  simpa only [matrixEntry_prepared_master base b hf rp n N W z rows low] using hc regs j v hv

private theorem forallTwo_member {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {y : β} (hy : y∈ys) :
    ∃ x∈xs,R x y := by
  induction h with
  | nil => simp at hy
  | cons hxy ht ih =>
      rcases List.mem_cons.mp hy with rfl|hy
      · exact ⟨_,by simp,hxy⟩
      · obtain ⟨x,hx,hr⟩ := ih hy
        exact ⟨x,by simp [hx],hr⟩

theorem raw_pair_bounds {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows) :
    ∀ row∈rows,BucketProgram.preWordsBounded B row := by
  intro row hrow p hp
  obtain ⟨j,_,hjr⟩ := forallTwo_member hr hrow
  obtain ⟨v,_,hvp⟩ := forallTwo_member hjr hp
  have hlen := hvp.2
  unfold LayoutMatrixProgram.pairLength at hlen
  exact ⟨by omega,by omega⟩

theorem exportMatrix_eval (a : State 16 896) :
    Eval exportMatrix
      (2*(a.stacks 659).length+3+(7*(a.stacks 668).length+5+
        clearManyCost [668,669,846] (copyState 668 847 (clearState 659 a))))
      a (exportedState a) := by
  have hc := clear_eval 659 a
  have hp := copy_eval 668 847 659 (clearState 659 a)
    (by decide) (by decide) (by decide) (by simp [clearState])
  have he := clearMany_eval [668,669,846] (copyState 668 847 (clearState 659 a))
  simpa only [exportMatrix, exportedState, clearState,
    Function.update_of_ne (by decide : (668:Fin 896)≠659)]
    using hc.seq (hp.seq he)

theorem exportCost_le (a : State 16 896) (A : ℕ) (ha : WordBound A a) :
    exportCost a ≤ 21*A+17 := by
  have hc := clearState_wordBound 659 a A ha
  have hp : WordBound (2*A) (copyState 668 847 (clearState 659 a)) := by
    intro i
    by_cases hi : i=847
    · subst i
      simp only [copyState,StackRoutines.copyStacks,Function.update_self,List.length_append]
      exact (Nat.add_le_add (hc 668) (hc 847)).trans (by omega)
    · exact (copyState_frame _ _ _ _ hi ▸ hc i).trans (by omega)
  have hf := clearManyCost_le [668,669,846] _ (2*A) hp
  have h659 := ha 659
  have h668 := ha 668
  simp only [List.length_cons,List.length_nil] at hf
  unfold exportCost
  omega

theorem importAddressFrom_eval (src : Fin 896) (a : State 16 896)
    (hs : src∉([649,659,846,847] : List (Fin 896))) :
    Eval (importAddressFrom src)
      (clearManyCost [649,659,846,847] a+7*(a.stacks src).length+5)
      a (addressStateFrom src a) := by
  have h649 : src≠649 := by intro h; subst src; simp at hs
  have h659 : src≠659 := by intro h; subst src; simp at hs
  have hc := clearMany_eval [649,659,846,847] a
  have hp := copy_eval src 649 659 (clearManyState [649,659,846,847] a)
    h649 h659 (by decide) (by simp [clearMany_stacks])
  simpa only [importAddressFrom, addressStateFrom, clearMany_stacks, hs, ite_false,
    Nat.add_assoc]
    using hc.seq hp

theorem addressStateFrom_value (src : Fin 896) (a : State 16 896)
    (hs : src∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks 649=a.stacks src := by
  simp only [addressStateFrom,copyState,StackRoutines.copyStacks,Function.update_self,
    clearMany_stacks, hs, show (649:Fin 896)∈[649,659,846,847] by decide,
    ite_false, ite_true, if_true, List.append_nil]

theorem addressStateFrom_frame (src : Fin 896) (a : State 16 896) (i : Fin 896)
    (hi : i∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks i=a.stacks i := by
  have h649 : i≠649 := by intro h; subst i; simp at hi
  rw [addressStateFrom,copyState_frame _ _ _ _ h649,clearMany_stacks]
  simp only [hi, ite_false]

theorem addressStateFrom_wordBound (src : Fin 896) (a : State 16 896) (A : ℕ)
    (hs : src∉([649,659,846,847] : List (Fin 896))) (ha : WordBound A a) :
    WordBound A (addressStateFrom src a) := by
  have hc := clearMany_wordBound [649,659,846,847] a A ha
  intro i
  by_cases hi : i=649
  · subst i
    rw [addressStateFrom_value src a hs]
    exact ha src
  · simpa only [addressStateFrom,copyState_frame _ _ _ _ hi] using hc i

theorem commandFrom_eval (src : Fin 896) (a : State 16 896) (b : Data) (steps : ℕ)
    (hs : src∉([649,659,846,847] : List (Fin 896)))
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressStateFrom src a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    Eval (commandFrom src)
      (clearManyCost [649,659,846,847] a+7*(a.stacks src).length+5+
        (steps+exportCost (lowResultFrom src a b))) a
      (exportedState (lowResultFrom src a b)) := by
  have hl := eval_call_from_state localProgram id lowStacks (addressStateFrom src a)
    Function.injective_id lowStacks.injective ht
  exact (importAddressFrom_eval src a hs).seq
    (hl.seq (exportMatrix_eval (lowResultFrom src a b)))

/-- Reverse visitation has the same paid-copy and native-loader budget. -/
theorem commandFrom_run_space (src : Fin 896) (a : State 16 896) (b : Data)
    (steps T A : ℕ) (hs : src∉([649,659,846,847] : List (Fin 896)))
    (ha : WordBound A a) (htime : steps ≤ T)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressStateFrom src a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    ∃ total,total ≤ 36*A+22*T+35 ∧
      Trace (smallProgramFrom src) total (a.withPC (some (smallProgramFrom src).entry))
        ((exportedState (lowResultFrom src a b)).withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace (smallProgramFrom src) prefixSteps
          (a.withPC (some (smallProgramFrom src).entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+T+1) := by
  have had := addressStateFrom_wordBound src a A hs ha
  have hb : WordBound (A+T) b := by
    intro i
    have h := Subexp.SequentialProgram.trace_stack_length_le ht i
    change (b.stacks i).length ≤ ((addressStateFrom src a).stacks (lowStacks i)).length+steps at h
    exact h.trans (Nat.add_le_add (had _) htime)
  have hl : WordBound (A+T) (lowResultFrom src a b) :=
    embedState_wordBound id lowStacks (addressStateFrom src a) b (A+T) lowStacks.injective
      (fun i => (had i).trans (Nat.le_add_right _ _)) hb
  have hc := clearManyCost_le [649,659,846,847] a A ha
  have hsrc := ha src
  have hexport := exportCost_le (lowResultFrom src a b) (A+T) hl
  simp only [List.length_cons,List.length_nil] at hc
  let total := clearManyCost [649,659,846,847] a+7*(a.stacks src).length+5+
    (steps+exportCost (lowResultFrom src a b))+1
  have htotal : total ≤ 36*A+22*T+35 := by dsimp [total]; omega
  refine ⟨total,htotal,compiled_halt_trace (commandFrom_eval src a b steps hs ht) src 847,?_⟩
  have hin : dataBits (a.withPC (some (smallProgramFrom src).entry)) ≤ 896*A :=
    StreamResources.dataBits_le_mul _ ha
  intro prefixSteps intermediate hp hpre
  have hh := trace_dataBits (smallProgramFrom src) hpre
  omega

theorem leafFrom_run_space (src : Fin 896) (frame : State 40 896) (a : State 16 896) (b : Data)
    (steps T A : ℕ) (hs : src∉([649,659,846,847] : List (Fin 896))) (ha : WordBound A a) (htime : steps ≤ T)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressStateFrom src a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    ∃ total,total ≤ 36*A+22*T+35 ∧
      Trace (programFrom src) total
        ((embedState leafRegs id frame a).withPC (some (programFrom src).entry))
        ((embedState leafRegs id frame (exportedState (lowResultFrom src a b))).withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace (programFrom src) prefixSteps
          ((embedState leafRegs id frame a).withPC (some (programFrom src).entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+T+1) := by
  obtain ⟨total,hbound,htr,_⟩ := commandFrom_run_space src a b steps T A hs ha htime ht
  have hl : Trace (programFrom src) total
      ((embedState leafRegs id frame a).withPC (some (programFrom src).entry))
      ((embedState leafRegs id frame (exportedState (lowResultFrom src a b))).withPC none) := by
    simpa [ProgramLinking.embedCfg,ProgramLinking.relocatePc,embedState,
      StructuredProgram.State.withPC,ProgramLinking.liftProgram,programFrom] using
      ProgramLinking.liftProgram_trace (smallProgramFrom src) leafRegs id (frame.withPC none)
        leafRegs.injective Function.injective_id htr
  refine ⟨total,hbound,hl,?_⟩
  have hin : dataBits ((embedState leafRegs id frame a).withPC (some (programFrom src).entry)) ≤ 896*A := by
    apply StreamResources.dataBits_le_mul
    intro i
    rw [show ((embedState leafRegs id frame a).withPC (some (programFrom src).entry)).stacks i=
      a.stacks i from embedState_stack leafRegs id frame a Function.injective_id i]
    exact ha i
  intro prefixSteps intermediate hp hpre
  have h := trace_dataBits (programFrom src) hpre
  omega


theorem leafInputFrom_masters (src : Fin 896) (frame : State 40 896) (base : Data)
    (hf : MasterFrame base (projectState leafRegs lowStacks frame)) :
    MasterFrame base (leafInputFrom src frame) := by
  constructor
  intro i hi
  have hnot : lowStacks i∉([649,659,846,847] : List (Fin 896)) := by
    simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (addressStateFrom_frame src (projectState leafRegs id frame) (lowStacks i) hnot).trans
    (hf.stored i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rowCountOutputs_protected : ∀ p∈rowCountOutputs,Protected p.2 := by simp [rowCountOutputs,Protected,temporary]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
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

theorem bootState_dimension (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 647=List.replicate records.length true := by
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ 647 (by decide)]
  · exact returned_word rowCountRegs (by decide) rowCountInputs rowCountOutputs _ _
      rowCountOutputs_protected (by decide) (2,647) (by simp [rowCountOutputs])
  · simp [cacheOutputs]


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

theorem nodeStart_dimension (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (nodeStart a ra rd rc r t records height R width words).stacks 647=List.replicate records.length true := by
  simp only [nodeStart,tupleInitialized,Function.update_of_ne (show (647:Fin 768)≠665 by decide),
    Function.update_of_ne (show (647:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 647 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_dimension a ra rd rc r t records height R width words

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- The actual native producer supplies the entry contract for this loader.
Only physical source/cache correctness is required, as obtained from the paid
node bootstrap; there is no matrix evaluator or supplied output table. -/
theorem native_local_eval (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (b : Data) (hf : MasterFrame (Native.start s a ra rd rc words) b)
    (z : ℕ) (hz : b.stacks 649=unary z) :
    ∃ rp rm rs raw shifted t,
      t ≤ localBudget b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted
        s.columnTime s.columnLength s.D ∧
      Eval localCommand t b (localResult b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (b.stacks 141))) raw shifted ∧
      (localResult b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks 668=
        Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words) ∧
      (localResult b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks 669=[] ∧
      ∀ A,WordBound A b → t ≤ localWork s z A := by
  have hb (i : Fin 768) (hm : i∈masters) (hi : i.val<340) : b.stacks i=a.stacks i :=
    (hf.stored i hm).trans (Native.start_low s a ra rd rc words i hi)
  obtain ⟨rp,tp,htp,hep⟩ := prepareHead_eval b s.n s.N s.rows s.low (s.Q*s.r) z
    ((hb 128 (by decide) (by decide)).trans ha.ambient) ((hb 129 (by decide) (by decide)).trans ha.factors)
    ((hb 134 (by decide) (by decide)).trans ha.low) hz ((hb 133 (by decide) (by decide)).trans ha.words)
    ((hb 132 (by decide) (by decide)).trans ha.wordWidth) s.rows_width s.rows_length
  let p := preparedHead b rp s.n s.N s.rows s.low (s.Q*s.r) z
  have hD : b.stacks 647=unary s.D := by
    rw [hf.stored 647 (by decide)]
    simpa only [Native.start,s.records_length] using
      nodeStart_dimension a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words
  have hp647 : p.stacks 647=unary s.D :=
    (preparedHead_frame b rp s.n s.N s.rows s.low (s.Q*s.r) z 647
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hD
  have hc := entryContract_prepared_master Native.entry _ b hf rp s.n s.N (s.Q*s.r) z s.rows s.low
    s.valid s.relation s.columnTime s.columnLength
    (Native.initial_contract s a ha ra rd rc words hw)
  obtain ⟨rm,raw,tm,hr,htm,hem,hom,hmb⟩ := raw_eval p s.D s.n
    (selectedHeads s.n s.rows s.low z) hp647
    (by simpa [p,LayoutMatrixProgram.ids_eq_indices] using
      preparedHead_ids b rp s.n s.N s.rows s.low (s.Q*s.r) z)
    s.valid s.relation s.columnTime s.columnLength hc
    (by intro j hj v hv; exact ⟨hj,HeadIdentifierProgram.chosenIds_bound _ _ v hv⟩)
    (by intro v hv; exact (HeadIdentifierProgram.chosenIds_bound _ _ v hv).le)
  let m := returned id (by decide) matrixInputs rawOutputs p
    (LayoutMatrixProgram.finalState (matrixBase p) rm raw)
  obtain ⟨rs,shifted,ts,hys,hts,hes,hos,hsb⟩ := shift_eval m raw hom
  let e := returned shiftRegs (by decide) shiftInputs shiftOutputs m
    (BucketProgram.preMatrixState rs (m.stacks 141) []
      (Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words)))
  have hm141 : m.stacks 141=b.stacks 141 :=
    (returned_frame id (by decide) matrixInputs rawOutputs p _ 141
      (by decide) (by simp [rawOutputs])).trans
      (preparedHead_frame b rp s.n s.N s.rows s.low (s.Q*s.r) z 141
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨rp,rm,rs,raw,shifted,tp+(tm+(ts+(2*(e.stacks 669).length+3))),
    ?_,hep.seq (hem.seq (hes.seq (clear_eval 669 e))),hr,?_,?_,?_,?_⟩
  · exact Nat.add_le_add htp (Nat.add_le_add htm (Nat.add_le_add_right hts _))
  · simpa only [hm141] using hys
  · simpa only [localResult,clearState,Function.update_of_ne (by decide : (668:Fin 768)≠669)] using hos
  · simp [localResult,clearState]
  · intro A hA
    let size := Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z
    let matrix := LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n
      (selectedHeads s.n s.rows s.low z)+1
    let live := A+5*size^2+matrix
    let shift := 10000*(s.D+1)*(s.n+1)*(live+s.columnLength+1)^2
    have hpB := Bounds.prepareHead_bound b rp s.n s.N s.rows s.low (s.Q*s.r) z A hA
      (by have hh := s.rows_length; omega)
    have hmB := hmb (A+5*size^2) hpB.1
    have hmW : (m.stacks 141).length ≤ live+s.columnLength :=
      (hmB.2 141).trans (Nat.le_add_right _ _)
    have hpairs := raw_pair_bounds hr
    obtain ⟨hrows,hwrows⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
    have hlen := Bounds.selectedHeads_length s.n s.rows s.low z
    have hsB := hsb live (live+s.columnLength) s.n hmB.2 hmW (by
      intro row hrow
      refine ⟨?_,(hwrows row hrow).le.trans hlen⟩
      intro pair hpair
      have hh := hpairs row hrow pair hpair
      exact ⟨hh.1.trans (Nat.le_add_left _ _),hh.2.trans (Nat.le_add_left _ _)⟩)
    rw [hrows] at hsB
    have he669 : (e.stacks 669).length ≤ live+shift := hsB.2 669
    have hpCost : tp ≤ 100000*(A+size^3+1) := htp.trans hpB.2
    change tp+(tm+(ts+(2*(e.stacks 669).length+3))) ≤
      100000*(A+size^3+1)+(matrix+1878*(live+1))+
        (shift+147*(live+shift+1))+(2*(live+shift)+3)
    have hmCost : tm ≤ matrix+1878*(live+1) := hmB.1
    have hsCost : ts ≤ shift+147*(live+shift+1) := hsB.1
    omega

/-- A complete fixed40-register head reload follows from actual native
bootstrap data. The same halted run has exact full integer rows and both
resource bounds; it does not assume a successful local execution. -/
theorem native_leafFrom_run_space_oai (src : Fin 896) (s : Native.Inputs)
    (a : Data) (ha : Native.Ready s a) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (words : List (List Bool)) (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hf : MasterFrame (Native.start s a ra rd rc words) (projectState leafRegs lowStacks frame))
    (z A : ℕ) (hs : src∉([649,659,846,847] : List (Fin 896)))
    (hz : frame.stacks src=unary z)
    (hA : WordBound A frame) :
    ∃ rp rm rs raw shifted total,
      total ≤ 36*A+22*(localWork s z A+1)+35 ∧
      Trace (programFrom src) total (frame.withPC (some (programFrom src).entry))
        ((leafOutputFrom src frame (localResult (leafInputFrom src frame) rp rm rs
          s.n s.N (s.Q*s.r) z s.rows s.low raw shifted)).withPC none) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace (programFrom src) prefixSteps (frame.withPC (some (programFrom src).entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+(localWork s z A+1)+1) := by
  let outer := projectState leafRegs id frame
  let b := leafInputFrom src frame
  have houter : WordBound A outer := hA
  have hb : WordBound A b := fun i =>
    addressStateFrom_wordBound src outer A hs houter (lowStacks i)
  have hbz : b.stacks 649=unary z :=
    (addressStateFrom_value src outer hs).trans hz
  have hb141 : b.stacks 141=frame.stacks 141 :=
    addressStateFrom_frame src outer 141 (by decide)
  obtain ⟨rp,rm,rs,raw,shifted,t,_,he,hr,hy,_,_,hc⟩ := native_local_eval s a ha
    ra rd rc words hw b (leafInputFrom_masters src frame _ hf) z hbz
  have tr := compiled_halt_trace he 649 668
  obtain ⟨total,ht,htr,hprefix⟩ := leafFrom_run_space src frame outer _ (t+1)
    (localWork s z A+1) A hs houter (Nat.add_le_add_right (hc A hb) 1) tr
  have hframe : embedState leafRegs id frame outer=frame :=
    embedState_project leafRegs id frame leafRegs.injective Function.injective_id
  rw [hframe] at htr hprefix
  exact ⟨rp,rm,rs,raw,shifted,total,ht,htr,hr,by simpa only [hb141] using hy,hprefix⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space_oai
