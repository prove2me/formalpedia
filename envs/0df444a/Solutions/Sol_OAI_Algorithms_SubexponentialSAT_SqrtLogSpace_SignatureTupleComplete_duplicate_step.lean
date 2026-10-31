-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.duplicate_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:54:17.150311+00:00
-- url     : https://prove2.me/submissions/a633aa30-ae0e-4fc9-bbc5-b2fe9a29f537

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_scan_kernel
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_scanner_caps_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_duplicate_run_space

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Width preservation below a binary overflow boundary

The input word may contain high zero bits. This lemma applies to actual ripple
increment results and does not assume a canonical binary representation.
-/

namespace SubexponentialSAT.CounterPrograms

/-- Increment stays within an n-bit word when its new value is below 2^n. -/
theorem increment_length_le_of_lt (bs : List Bool) (n : ℕ)
    (hlen : bs.length ≤ n) (hvalue : value bs + 1 < 2 ^ n) :
    (ripple true bs).length ≤ n := by
  induction n generalizing bs with
  | zero =>
      have he : bs = [] := List.length_eq_zero_iff.mp (by omega)
      subst bs
      simp at hvalue
  | succ n ih =>
      cases bs with
      | nil => simp [ripple]
      | cons bit bs =>
          cases bit with
          | false => simpa [ripple] using hlen
          | true =>
              have hl : bs.length ≤ n := by simpa using hlen
              have hv : value bs + 1 < 2 ^ n := by
                simp only [value, Bool.toNat_true, pow_succ] at hvalue
                omega
              simpa [ripple] using Nat.succ_le_succ (ih bs hl hv)

end SubexponentialSAT.CounterPrograms

end OAI.Algorithms
end

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

/-- The actual ripple increment remains the next fixed-width word before overflow. -/
theorem increment_word {width : ℕ} (i : Fin (2 ^ width)) (h : i.val + 1 < 2 ^ width) :
    ripple true (wordEquiv width i).val = (wordEquiv width ⟨i.val + 1, h⟩).val := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · apply Nat.le_antisymm
    · exact (increment_length_le_of_lt (wordEquiv width i).val width
        (wordEquiv width i).property.le (by simpa [wordEquiv,
          ExecCNFTupleEnumeration.fixedBits_value width i i.isLt] using h)).trans_eq
          (wordEquiv width ⟨i.val + 1, h⟩).property.symm
    · have hlen : (wordEquiv width i).val.length ≤
          (ripple true (wordEquiv width i).val).length := by
        generalize (wordEquiv width i).val = xs
        induction xs with
        | nil => simp
        | cons b xs ih =>
            cases b
            · simp [ripple]
            · simp only [ripple, ↓reduceIte, Bool.not_true, List.length_cons] at *
              omega
      simpa only [(wordEquiv width i).property,
        (wordEquiv width ⟨i.val + 1, h⟩).property] using hlen
  · simp [wordEquiv, value_increment, ExecCNFTupleEnumeration.fixedBits_value, i.isLt, h]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

theorem duplicateScan_eq_true_iff [DecidableEq κ] (key : ℕ → κ) (candidate bound : ℕ) :
    duplicateScan key candidate bound = true ↔ ∃ j < bound, key j = key candidate := by
  induction bound with
  | zero => simp [duplicateScan]
  | succ bound ih =>
    simp only [duplicateScan, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨j, hj, he⟩ | he)
      · exact ⟨j, Nat.lt_succ_of_lt hj, he⟩
      · exact ⟨bound, Nat.lt_succ_self _, he⟩
    · rintro ⟨j, hj, he⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact Or.inl ⟨j, hj, he⟩
      · exact Or.inr he

theorem duplicateScan_eq_false_iff [DecidableEq κ] (key : ℕ → κ) (candidate bound : ℕ) :
    duplicateScan key candidate bound = false ↔ ∀ j < bound, key j ≠ key candidate := by
  rw [← Bool.not_eq_true, duplicateScan_eq_true_iff]
  simp

theorem rescan_emits_iff [DecidableEq κ] (key : ℕ → κ) (i : Fin N) :
    duplicateScan key i i = false ↔ ∀ j : Fin N, j < i → key j ≠ key i := by
  rw [duplicateScan_eq_false_iff]
  constructor
  · intro h j hj
    exact h j hj
  · intro h j hj
    exact h ⟨j, hj.trans i.isLt⟩ hj

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedWords_length {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) : xs.length=ys.length := by
  induction h with
  | nil => rfl
  | cons h hs ih => simpa using ih

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer semantics and explicit polynomial bounds for the concrete
signed-coefficient preprocessing machine. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedMatrix_rowWidth {W : List Bool} {xs : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) xs ys)
    (width : ℕ) (hw : ∀ row∈xs, row.length=width) :
    ∀ row∈ys, row.length=width := by
  induction h with
  | nil => simp
  | @cons a y xs ys hy hys ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (shiftedWords_length hy).symm.trans (hw a (by simp))
      · exact ih (fun a ha => hw a (by simp [ha])) z hz

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
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

/-- The physical shifted rows retain every incidence and the exact emitted
column order, including empty matrices and empty heads. -/
theorem shiftedMatrix_typed (W : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (B D : ℕ)
    (js : List ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys) :
    ∃ c : Fin D → Fin js.length → List Bool,
      ys = List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i, ∃ p, Rel j.val (js.get i) p ∧
        LayoutMatrixProgram.pairLength p ≤ B ∧ BucketProgram.shiftedWord W p (c j i) := by
  obtain ⟨hlen, hrow⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hylen : ys.length = D := hy.length_eq.symm.trans hlen
  have hyrow : ∀ row ∈ ys, row.length = js.length :=
    BucketProgram.shiftedMatrix_rowWidth hy js.length hrow
  let rowAt (j : Fin D) : List (List Bool) := ys.get ⟨j.val, by omega⟩
  have hrowAt (j : Fin D) : (rowAt j).length = js.length :=
    hyrow _ (List.get_mem _ _)
  let c (j : Fin D) (i : Fin js.length) : List Bool :=
    (rowAt j).get ⟨i.val, by rw [hrowAt]; exact i.isLt⟩
  refine ⟨c, ?_, ?_⟩
  · apply List.ext_get
    · simp [hylen]
    · intro j hj hj'
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      apply List.ext_get
      · simp [← hrowAt ⟨j, by simpa using hj'⟩, rowAt]
      · intro i hi hi'
        simp only [List.get_eq_getElem, List.getElem_ofFn]
        rfl
  · intro j i
    have hjraw : j.val < raw.length := by omega
    have hjrange : j.val < (List.range D).length := by simp
    have hrawrow := hr.get hjrange hjraw
    simp only [List.get_eq_getElem, List.getElem_range] at hrawrow
    have hshiftrow := hy.get hjraw (by omega)
    have hiraw : i.val < (raw.get ⟨j.val,hjraw⟩).length := by
      change i.val < (raw[j.val]'hjraw).length
      rw [← hrawrow.length_eq]
      exact i.isLt
    have hiy : i.val < (ys.get ⟨j.val,by omega⟩).length := by
      exact (hrowAt j).symm ▸ i.isLt
    have hp := hrawrow.get i.isLt hiraw
    have hs := hshiftrow.get hiraw hiy
    exact ⟨_, hp.1, hp.2, hs⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem advanceState_candidate (a : State 40 896) :
    (advanceState a).stacks candidatePorts.counter =
      CounterPrograms.ripple true (a.stacks candidatePorts.counter) := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks candidatePorts.counter = _
  rw [← CounterForPrograms.nextState_outside remainingPorts
    (Counters.incrementResult candidatePorts a) candidatePorts.counter
    (by decide) (by decide)]
  exact Counters.incrementResult_counter _ _

theorem advanceState_remaining (a : State 40 896)
    (hcs : a.stacks candidatePorts.scratch = []) :
    (advanceState a).stacks remainingPorts.counter =
      CounterPrograms.ripple false (a.stacks remainingPorts.counter) := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks remainingPorts.counter = _
  rw [CounterForPrograms.nextState_counter, Counters.incrementResult_stacks candidatePorts a hcs]
  rw [Function.update_of_ne (by decide : remainingPorts.counter ≠ candidatePorts.counter)]

/-- Binary words remain short even at the final overflow to the exact bound.
The exhausted word is never passed to the signature evaluator. -/
theorem advanceState_widths (a : State 40 896) (width : ℕ)
    (hcs : a.stacks candidatePorts.scratch = [])
    (hc : (a.stacks candidatePorts.counter).length ≤ width + 1)
    (hrlen : (a.stacks remainingPorts.counter).length ≤ width + 1)
    (hr : 0 < CounterPrograms.value (a.stacks remainingPorts.counter))
    (htotal : CounterPrograms.value (a.stacks candidatePorts.counter) +
      CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ width) :
    ((advanceState a).stacks candidatePorts.counter).length ≤ width + 1 ∧
      ((advanceState a).stacks remainingPorts.counter).length ≤ width + 1 := by
  constructor
  · rw [advanceState_candidate]
    apply CounterPrograms.increment_length_le_of_lt _ _ hc
    have hp : 0 < 2 ^ width := Nat.pow_pos (by decide)
    rw [pow_succ]
    omega
  · rw [advanceState_remaining a hcs, CounterPrograms.decrement_length hr]
    exact hrlen

theorem testAvailableState_flag (a : State 40 896) :
    (testAvailableState a).regs controllerPorts.available =
      !(CounterPrograms.isZero (a.stacks remainingPorts.counter)) :=
  CounterForPrograms.testResult_flag remainingPorts a

/-- Every nonterminal cursor is exactly the fixed-width word consumed by the
attained-signature predicate, not merely a short encoding of the same value. -/
theorem advanceState_assignment (a : State 40 896) (h : ℕ) (candidate : Fin (2 ^ h))
    (hc : a.stacks candidatePorts.counter = ExecCNFTupleEnumeration.fixedBits h candidate)
    (hn : candidate.val + 1 < 2 ^ h) :
    (advanceState a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits h (candidate.val + 1) := by
  rw [advanceState_candidate, hc]
  exact Counters.increment_word candidate hn

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

section KeyEncoding

/-- The byte-key rescan's actual fresh bit is exactly the first-occurrence
predicate of the stable mathematical full signature. -/
theorem actual_fresh_iff_model {n : ℕ} {A B : Type*} [DecidableEq A]
    (actual : ℕ → A) (model : Fin n → B)
    (hkernel : ∀ i j : Fin n, actual i = actual j ↔ model i = model j)
    (candidate : Fin n) :
    (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true ↔
      ∀ j, j < candidate → model j ≠ model candidate := by
  have hb : (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true ↔
      AttainedSignatures.duplicateScan actual candidate candidate = false := by
    cases AttainedSignatures.duplicateScan actual candidate candidate <;> decide
  rw [hb, AttainedSignatures.rescan_emits_iff]
  constructor
  · intro hf j hj he
    exact hf j hj ((hkernel j candidate).mpr he)
  · intro hf j hj he
    exact hf j hj ((hkernel j candidate).mp he)

theorem actual_duplicate_iff_model {n : ℕ} {A B : Type*} [DecidableEq A]
    (actual : ℕ → A) (model : Fin n → B)
    (hkernel : ∀ i j : Fin n, actual i = actual j ↔ model i = model j)
    (candidate : Fin n) :
    (!(AttainedSignatures.duplicateScan actual candidate candidate)) = false ↔
      ¬ ∀ j, j < candidate → model j ≠ model candidate := by
  have hb : (!(AttainedSignatures.duplicateScan actual candidate candidate)) = false ↔
      ¬ (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true := by
    cases !(AttainedSignatures.duplicateScan actual candidate candidate) <;> decide
  exact hb.trans (not_congr (actual_fresh_iff_model actual model hkernel candidate))

end KeyEncoding

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

theorem initializeFreshState_word (a : State 40 896) :
    (initializeFreshState a).stacks (rescanStacks 22) = [false] := by
  simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, clearState]

/-- Decrement retains the full `h+1`-bit remaining word, including leading
zeros. This matches the suspended-frame encoding after every candidate. -/
theorem remaining_word_after_advance (a : State 40 896) (h candidate : ℕ)
    (hc : candidate < 2 ^ h)
    (hs : a.stacks candidatePorts.scratch = [])
    (hr : a.stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h - candidate)) :
    (advanceState a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h - (candidate + 1)) := by
  have hpow : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have hbound : 2 ^ h - candidate < 2 ^ (h + 1) := by
    rw [pow_succ]
    omega
  have hnext : 2 ^ h - (candidate + 1) < 2 ^ (h + 1) := by
    rw [pow_succ]
    omega
  have hv : CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - candidate := by
    rw [hr]
    exact ExecCNFTupleEnumeration.fixedBits_value _ _ hbound
  have hp : 0 < CounterPrograms.value (a.stacks remainingPorts.counter) := by omega
  rw [advanceState_remaining a hs]
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · rw [CounterPrograms.decrement_length hp, hr]
    simp
  · rw [ExecCNFTupleEnumeration.fixedBits_value _ _ hnext]
    have hd := CounterPrograms.value_decrement hp
    omega

theorem rescan_embed_controller (frame : State 40 896) (callee : State 16 24)
    (j : Fin 40) (hj : 16 ≤ j.val) :
    (embedState rescanRegisters rescanStacks frame callee).regs j = frame.regs j := by
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  dsimp [rescanRegisters] at hv
  omega

theorem candidateOutput_flag (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val) :
    (candidateOutput frame regs W rows h candidate).regs j = frame.regs j :=
  rescan_embed_controller _ _ j hj

theorem candidateOutput_fresh (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) :
    (candidateOutput frame regs W rows h candidate).stacks (rescanStacks 22) =
      [!(AttainedSignatures.duplicateScan
        (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate)] := by
  rw [candidateOutput, embedState_stack _ _ _ _ rescanStacks.injective]
  rfl


theorem testAvailableState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (testAvailableState a).stacks = a.stacks :=
  CounterForPrograms.testResult_stacks remainingPorts a hs

theorem initializeFreshState_controller (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (initializeFreshState a).regs j = a.regs j := by
  simp only [initializeFreshState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    execInstr, Function.update_of_ne h0]
  exact StackRoutines.readRegs_frame a.regs 0 1 j none h0 h1

theorem probePostState_flags (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h))
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    (probePostState a out W rows h candidate).regs controllerPorts.available = true ∧
      (probePostState a out W rows h candidate).regs controllerPorts.fresh =
        !(AttainedSignatures.duplicateScan
          (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate) := by
  have hw := candidateOutput_fresh (probePreState a) out W rows h candidate
  simp only [rescanStacks_fresh] at hw
  have hav : (candidateOutput (probePreState a) out W rows h candidate).regs
      controllerPorts.available = true := by
    rw [candidateOutput_flag _ _ _ _ _ _ _ (by decide)]
    rw [probePreState, initializeFreshState_controller _ _ (by decide) (by decide)]
    rw [testAvailableState_flag, hnonzero]
    rfl
  constructor
  · simpa [probePostState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hw, controllerPorts] using hav
  · simp [probePostState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hw, controllerPorts]


theorem initializeFreshState_stacks (a : State 40 896) :
    (initializeFreshState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  funext i
  by_cases hi : i = rescanStacks 22
  · subst i
    rw [Function.update_self, initializeFreshState_word]
  · simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, clearState]

theorem probePreState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePreState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  rw [probePreState, initializeFreshState_stacks, testAvailableState_stacks a hs]

/-- Preparing a candidate changes only the latch word. The whole fixed local
input projection is then the one used in the proved native rescan theorem. -/
theorem CandidateReady.probe_projection {a : State 40 896} {W : List Bool}
    {rows : List (List (List Bool))} {h : ℕ} {candidate : Fin (2 ^ h)}
    (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    projectState rescanRegisters rescanStacks (probePreState a) =
      AttainedSignatureProgram.Rescan.workState
        ((probePreState a).regs ∘ rescanRegisters) W rows
        (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change (probePreState a).stacks (rescanStacks i) = _
  rw [probePreState_stacks a hs]
  have hf (j : Fin 24) (hj : j ≠ 22) : rescanStacks j ≠ rescanStacks 22 :=
    fun he => hj (rescanStacks.injective he)
  by_cases h22 : i = 22
  · subst i
    rw [Function.update_self]
    rfl
  rw [Function.update_of_ne (hf i h22)]
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  by_cases h16 : i = 16
  · subst i; exact ready.current
  by_cases h17 : i = 17
  · subst i; exact ready.saved
  by_cases h18 : i = 18
  · subst i; exact ready.predecessor
  rw [ready.scratch i h0 h15 h16 h17 h18 h22]
  fin_cases i <;> simp_all

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

theorem CursorWords.remaining_value {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - c := by
  rw [hw.remaining]
  apply ExecCNFTupleEnumeration.fixedBits_value
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

theorem CursorWords.available {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.isZero (a.stacks remainingPorts.counter) = decide (c = 2 ^ h) := by
  have hv := hw.remaining_value
  have hr := hw.range
  by_cases he : c = 2 ^ h
  · simp only [he, decide_true]
    apply (CounterPrograms.isZero_eq_true_iff _).mpr
    rw [hv, he, Nat.sub_self]
  · simp only [he, decide_false]
    apply (CounterPrograms.isZero_eq_false_iff _).mpr
    omega

theorem CursorWords.advance {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) (hc : c < 2 ^ h) :
    CursorWords (advanceCandidateState a) h (c + 1) := by
  have hp : 0 < CounterPrograms.value (a.stacks remainingPorts.counter) := by
    rw [hw.remaining_value]
    omega
  have hwidth := advanceState_widths a h hw.incrementScratch hw.width
    (by rw [hw.remaining]; simp) hp (by rw [hw.value, hw.remaining_value]; omega)
  have hcandidate : (advanceCandidateState a).stacks candidatePorts.counter =
      (advanceState a).stacks candidatePorts.counter := by
    exact Function.update_of_ne (by decide : candidatePorts.counter ≠ tupleStacks 3) [] (advanceState a).stacks
  have hremaining : (advanceCandidateState a).stacks remainingPorts.counter =
      (advanceState a).stacks remainingPorts.counter := by
    exact Function.update_of_ne (by decide : remainingPorts.counter ≠ tupleStacks 3) [] (advanceState a).stacks
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcandidate, advanceState_candidate, CounterPrograms.value_increment, hw.value]
  · rw [hcandidate]
    exact hwidth.1
  · intro hn
    rw [hcandidate]
    exact advanceState_assignment a h ⟨c, hc⟩ (hw.exact hc) hn
  · rw [hremaining]
    exact remaining_word_after_advance a h c hc hw.incrementScratch hw.remaining
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] candidatePorts.scratch = []
    rw [Function.update_of_ne (by decide)]
    rw [advanceState_outside a hw.incrementScratch candidatePorts.scratch
      (by decide) (by decide) (by decide), hw.incrementScratch]
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] remainingPorts.scratch = []
    rw [Function.update_of_ne (by decide)]
    exact CounterForPrograms.nextState_scratch remainingPorts _


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureRescanBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Physical effects of one full-signature probe

The input readiness facts describe actual words. The native predicate itself
supplies the run; its returned freshness is the first-occurrence predicate for
the complete integer signature.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open AttainedSignatureProgram.Rescan

theorem probe_stacks (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePostState a out W rows h candidate).stacks =
      Function.update (Function.update a.stacks (rescanStacks 17)
        (naturalKey W rows h candidate)) (rescanStacks 22)
        [!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)] := by
  classical
  let pre := probePreState a
  let initial := workState (pre.regs ∘ rescanRegisters) W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) []
    (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] []
  let key := naturalKey W rows h candidate
  let fresh := !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)
  have hz : ExecCNFTupleEnumeration.fixedBits h 0 = List.replicate h false :=
    ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
      (by simp [ExecCNFTupleEnumeration.fixedBits_value h 0 (Nat.pow_pos (by decide))])
  have hlocal : (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      key (List.replicate h false) [] fresh [] []).stacks =
      Function.update (Function.update initial.stacks 17 key) 22 [fresh] := by
    dsimp [initial]
    rw [hz]
    funext i
    fin_cases i <;> simp [workState]
  have hemb : Function.extend rescanStacks initial.stacks pre.stacks = pre.stacks := by
    change (embedState rescanRegisters rescanStacks pre initial).stacks = pre.stacks
    have hi : projectState rescanRegisters rescanStacks pre = initial := ready.probe_projection hs
    rw [← hi, embedState_project _ _ _ rescanRegisters.injective rescanStacks.injective]
  change Function.extend rescanStacks _ pre.stacks = _
  rw [hlocal, ProgramLinking.extend_update rescanStacks.injective,
    ProgramLinking.extend_update rescanStacks.injective, hemb]
  change Function.update (Function.update (probePreState a).stacks (rescanStacks 17) key)
    (rescanStacks 22) [fresh] = _
  rw [probePreState_stacks a hs]
  funext j
  by_cases h17 : j = rescanStacks 17
  · subst j
    simp only [Function.update_self, Function.update_of_ne
      (by decide : rescanStacks 17 ≠ rescanStacks 22)]
    rfl
  · by_cases h22 : j = rescanStacks 22
    · subst j; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne h17, Function.update_of_ne h22]

theorem probe_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) (j : Fin 896)
    (hk : j ≠ rescanStacks 17) (hf : j ≠ rescanStacks 22) :
    (probePostState a out W rows h candidate).stacks j = a.stacks j := by
  rw [probe_stacks a out W rows h candidate ready hs]
  rw [Function.update_of_ne hf, Function.update_of_ne hk]

theorem probe_preserves_cursor (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (cursor : CursorWords a h candidate) :
    CursorWords (probePostState a out W rows h candidate) h candidate := by
  have hc := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    candidatePorts.counter (by decide) (by decide)
  have hr := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    remainingPorts.counter (by decide) (by decide)
  have hcs := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    candidatePorts.scratch (by decide) (by decide)
  have hrs := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    remainingPorts.scratch (by decide) (by decide)
  exact ⟨cursor.range, hc ▸ cursor.value, hc ▸ cursor.width,
    fun hi => hc.trans (cursor.exact hi), hr.trans cursor.remaining,
    hcs.trans cursor.incrementScratch, hrs.trans cursor.decrementScratch⟩

theorem test_available_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (ha : j ≠ controllerPorts.available) :
    (testAvailableState a).regs j = a.regs j := by
  have h2 : j ≠ remainingPorts.register 2 := by
    intro he
    have hv := congrArg Fin.val he
    change j.val = 2 at hv
    omega
  simp only [testAvailableState, CounterForPrograms.testResult,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne ha, Function.update_of_ne h2]
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  change i.val = j.val at hv
  omega

theorem probe_register_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val)
    (ha : j ≠ controllerPorts.available) (hf : j ≠ controllerPorts.fresh) :
    (probePostState a out W rows h candidate).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro he; subst j; norm_num at hj
  change readRegs (candidateOutput (probePreState a) out W rows h candidate).regs
    controllerPorts.fresh 0 _ j = _
  rw [StackRoutines.readRegs_frame _ _ _ _ _ hf h0,
    candidateOutput_flag _ _ _ _ _ _ _ hj]
  rw [probePreState, initializeFreshState_controller _ _ h0 h1]
  exact test_available_register_frame a j (by omega) ha

theorem probe_control_flags (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h))
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    (probePostState a out W rows h candidate).regs controllerPorts.active =
        a.regs controllerPorts.active ∧
      (probePostState a out W rows h candidate).regs controllerPorts.leaf =
        a.regs controllerPorts.leaf ∧
      (probePostState a out W rows h candidate).regs controllerPorts.available = true ∧
      (probePostState a out W rows h candidate).regs controllerPorts.fresh =
        !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate) :=
  ⟨probe_register_frame a out W rows h candidate _ (by decide) (by decide) (by decide),
    probe_register_frame a out W rows h candidate _ (by decide) (by decide) (by decide),
    probePostState_flags a out W rows h candidate hnonzero⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual state refinements for the fixed attained-signature controller.
Each lemma follows concrete commands already installed in the native ABI. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal


theorem counter_install_register_frame (p : CounterForPrograms.Ports 40 896)
    (a : State 40 896) (b present flag : Bool) (xs ys : List Bool) (j : Fin 40)
    (hj : ¬ ∃ i, p.register i = j) :
    (CounterForPrograms.install p a b present flag xs ys).regs j = a.regs j :=
  embedState_register_frame _ _ _ _ _ hj

theorem lowCounter_register_avoids (j : Fin 40) (hj : 3 ≤ j.val) :
    (¬ ∃ i, candidatePorts.register i = j) ∧
      (¬ ∃ i, remainingPorts.register i = j) := by
  constructor <;> rintro ⟨i, hi⟩
  all_goals
    have hv := congrArg Fin.val hi
    have hil := i.isLt
    dsimp [candidatePorts, remainingPorts] at hv
    omega

theorem advanceState_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (hav : j ≠ controllerPorts.available) :
    (advanceState a).regs j = a.regs j := by
  have h2 : j ≠ remainingPorts.register 2 := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [remainingPorts] at hv
    omega
  have hreg := lowCounter_register_avoids j hj
  unfold advanceState CounterForPrograms.nextState CounterForPrograms.testResult
  simp only [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne hav, Function.update_of_ne h2]
  unfold CounterForPrograms.zeroResult
  rw [counter_install_register_frame _ _ _ _ _ _ _ j hreg.2]
  unfold CounterForPrograms.decrementResult
  rw [counter_install_register_frame _ _ _ _ _ _ _ j hreg.2]
  unfold Counters.incrementResult
  exact counter_install_register_frame _ _ _ _ _ _ _ j hreg.1

theorem advanceCandidateState_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (hav : j ≠ controllerPorts.available) :
    (advanceCandidateState a).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; have := congrArg Fin.val he; simp at this; omega
  have h1 : j ≠ 1 := by intro he; have := congrArg Fin.val he; simp at this; omega
  change readRegs (advanceState a).regs 0 1 none j = a.regs j
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1]
  exact advanceState_register_frame a j hj hav

theorem advanceCandidateState_outside (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = []) (i : Fin 896)
    (hk : i ≠ tupleStacks 3) (hc : i ≠ candidatePorts.counter)
    (hr : i ≠ remainingPorts.counter) (ht : i ≠ remainingPorts.scratch) :
    (advanceCandidateState a).stacks i = a.stacks i := by
  change Function.update (advanceState a).stacks (tupleStacks 3) [] i = a.stacks i
  rw [Function.update_of_ne hk, advanceState_outside a hs i hc hr ht]

/-- Scanner scratch is restored by each probe and is disjoint from both
binary counters. Thus advancing never requires a new allocation or scan. -/
theorem probe_advance_ready (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate next : Fin (2 ^ h)) (hnext : next.val = candidate.val + 1)
    (ready : CandidateReady a W rows h candidate) (hw : CursorWords a h candidate) :
    CandidateReady (advanceCandidateState (probePostState a out W rows h candidate))
      W rows h next := by
  let b := probePostState a out W rows h candidate
  have hb : CursorWords b h candidate :=
    SignatureRescanBridge.probe_preserves_cursor a out W rows h candidate ready hw
  have hn := hb.advance candidate.isLt
  have hf (i : Fin 896) (hk : i ≠ tupleStacks 3) (hc : i ≠ candidatePorts.counter)
      (hr : i ≠ remainingPorts.counter) (hs : i ≠ remainingPorts.scratch)
      (h17 : i ≠ rescanStacks 17) (h22 : i ≠ rescanStacks 22) :
      (advanceCandidateState b).stacks i = a.stacks i := by
    rw [advanceCandidateState_outside b hb.incrementScratch i hk hc hr hs]
    exact SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready
      hw.decrementScratch i h17 h22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.offset
  · rw [hf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.matrix
  · change (advanceCandidateState b).stacks candidatePorts.counter = _
    rw [hnext]
    exact hn.exact (by rw [← hnext]; exact next.isLt)
  · change Function.update (advanceState b).stacks (tupleStacks 3) [] (tupleStacks 3) = []
    exact Function.update_self _ _ _
  · rw [hf _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.predecessor
  · intro i h0 h15 h16 h17 h18 h22
    have hsmall : ∀ j : Fin 24, j ≠ 0 → j ≠ 15 → j ≠ 16 → j ≠ 17 → j ≠ 18 →
        (rescanStacks j).val < 768 := by decide
    have hv := hsmall i h0 h15 h16 h17 h18
    have hports : rescanStacks i ≠ tupleStacks 3 ∧
        rescanStacks i ≠ candidatePorts.counter ∧ rescanStacks i ≠ remainingPorts.counter ∧
        rescanStacks i ≠ remainingPorts.scratch ∧ rescanStacks i ≠ rescanStacks 17 ∧
        rescanStacks i ≠ rescanStacks 22 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro he; have he' := congrArg Fin.val he; change (rescanStacks i).val = 839 at he'; omega
      · intro he; have he' := congrArg Fin.val he; change (rescanStacks i).val = 838 at he'; omega
      · intro he; have he' := congrArg Fin.val he; change (rescanStacks i).val = 843 at he'; omega
      · intro he; have he' := congrArg Fin.val he; change (rescanStacks i).val = 841 at he'; omega
      · exact fun he => h17 (rescanStacks.injective he)
      · exact fun he => h22 (rescanStacks.injective he)
    rw [hf _ hports.1 hports.2.1 hports.2.2.1 hports.2.2.2.1
      hports.2.2.2.2.1 hports.2.2.2.2.2]
    exact ready.scratch i h0 h15 h16 h17 h18 h22

section AdvanceStorage

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- A completed candidate is advanced once. Its full key is discarded, while
both attained-prefix frame banks and the physical head address survive. -/
theorem advance_scan_storage (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (candidate : ℕ)
    (a : State 40 896)
    (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hw : CursorWords a (h depth.val) candidate) (hc : candidate < 2 ^ h depth.val)
    (hl : a.regs controllerPorts.leaf = false)
    (hp : a.stacks (tupleStacks 4) = [])
    (hz : a.stacks (tupleStacks 8) = List.replicate (h depth.val) false) :
    ScanStorage h key levels base depth ancestors (candidate + 1) (advanceCandidateState a) := by
  have hwords := hw.advance hc
  have hframe (i : Fin 896) (hk : i ≠ tupleStacks 3) (hcan : i ≠ candidatePorts.counter)
      (hrem : i ≠ remainingPorts.counter) (hs : i ≠ remainingPorts.scratch) :
      (advanceCandidateState a).stacks i = a.stacks i :=
    advanceCandidateState_outside a hw.incrementScratch i hk hcan hrem hs
  refine ⟨⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩, hwords, ?_, ?_, ?_, ?_⟩
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact ha.cursors
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact ha.representatives
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact ha.heads
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact ha.address
  · rw [advanceCandidateState_register_frame _ _ (by decide) (by decide)]
    exact ha.active
  · rw [advanceCandidateState_register_frame _ _ (by decide) (by decide)]
    exact hl
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] (tupleStacks 3) = []
    exact Function.update_self _ _ _
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact hp
  · rw [hframe _ (by decide) (by decide) (by decide) (by decide)]
    exact hz

end AdvanceStorage


/-- A losing candidate changes only its two cursor words and the freshness
latch. In particular all accumulators, retained inputs, and caches survive. -/
theorem duplicate_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hw : CursorWords a h candidate.val) (i : Fin 896)
    (hc : i ≠ candidatePorts.counter) (hr : i ≠ remainingPorts.counter)
    (hf : i ≠ rescanStacks 22) :
    (advanceCandidateState (probePostState a out W rows h candidate)).stacks i = a.stacks i := by
  let b := probePostState a out W rows h candidate
  have hb := SignatureRescanBridge.probe_preserves_cursor a out W rows h candidate ready hw
  have hn := hb.advance candidate.isLt
  by_cases hk : i = tupleStacks 3
  · subst i
    change Function.update (advanceState b).stacks (tupleStacks 3) [] (tupleStacks 3) = _
    rw [Function.update_self]
    exact ready.saved.symm
  · by_cases hs : i = remainingPorts.scratch
    · subst i
      rw [hn.decrementScratch, hw.decrementScratch]
    · rw [advanceCandidateState_outside b hb.incrementScratch i hk hc hr hs]
      exact SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready
        hw.decrementScratch i hk hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleBranchSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix composition for the actual exhausted and leaf branches of the
attained-signature controller. The component executions are the installed
probe, visitor and ascent commands, and every caller stack is covered. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative

/-- Inverting the installed body preserves its actual measured execution;
it does not choose a second run or replace the visitor. -/
theorem iteration_of_eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (he : Eval (body p q) n a b) :
    Iteration p q n a b := by
  cases he with
  | ite_true hl hleaf =>
    cases hleaf with
    | seq hv ha => exact .leaf hl hv ha
  | ite_false hl hscan =>
    cases hscan with
    | seq hp havailable =>
      cases havailable with
      | ite_false ha hasc =>
        simpa only [Nat.add_assoc] using Iteration.exhausted hl hp ha hasc
      | ite_true ha hfresh =>
        cases hfresh with
        | ite_true hf hd =>
          simpa only [Nat.add_assoc] using Iteration.fresh hl hp ha hf hd
        | ite_false hf hn =>
          simpa only [Nat.add_assoc] using Iteration.duplicate hl hp ha hf hn

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace
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


/-- All raw incidence rows are present in the scanner, with polynomial
coefficient word lengths. No coordinate grid is materialized. -/
theorem shifted_rows_bounds (s : Native.Inputs) (z L : ℕ) (W : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hW : W.length≤L)
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    shifted.length=s.D ∧
      (∀ row∈shifted, row.length=(selectedHeads s.n s.rows s.low z).length) ∧
      ∀ row∈shifted, ∀ x∈row, x.length≤3*(s.columnLength+L)+1 := by
  obtain ⟨c,hc,hentry⟩ := SignatureHeadLoader.shiftedMatrix_typed W s.relation
    s.columnLength s.D (selectedHeads s.n s.rows s.low z) raw shifted hr hy
  subst shifted
  refine ⟨by simp, ?_, ?_⟩
  · intro row hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    simp
  · intro row hrow x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨pair,_,hpair,hshift⟩ := hentry j i
    have hlength := hshift.2
    unfold LayoutMatrixProgram.pairLength at hpair
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Shared actual produced input data for the tuple controller and visitor.
The record contains source words, native readiness and paid cache semantics;
it contains no evaluator, resource contract, or successful execution premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

namespace ProducedSource

theorem headSize_le (s : ProducedSource) (depth : ℕ) : s.headSize depth ≤ s.input.n :=
  Bounds.selectedHeads_length ..

end ProducedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

private theorem master_not_candidate (i : Fin 768) : SignatureHeadLoader.lowStacks i≠candidatePorts.counter := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=838 at hv
  omega

private theorem master_not_remaining (i : Fin 768) : SignatureHeadLoader.lowStacks i≠remainingPorts.counter := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=843 at hv
  omega

private theorem master_not_fresh (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i≠rescanStacks 22 := by
  simp only [SignatureHeadLoader.masters,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- Losing-candidate scans preserve the actual source and native caches. -/
theorem duplicate_masters (s : ProducedSource) (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ) (candidate : Fin (2^h))
    (ready : CandidateReady a W rows h candidate) (hw : CursorWords a h candidate.val)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (advanceCandidateState (probePostState a out W rows h candidate))) := by
  constructor
  intro i hi
  exact (duplicate_stack_frame a out W rows h candidate ready hw _
    (master_not_candidate i) (master_not_remaining i) (master_not_fresh i hi)).trans (hm.stored i hi)

private theorem probe_advance_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (candidate : Fin (2^h depth.val))
    (a : State 40 896) (out : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool)))
    (ha : ScanStorage h key levels base depth ancestors candidate.val a)
    (ready : CandidateReady a W rows (h depth.val) candidate) :
    ScanStorage h key levels base depth ancestors (candidate.val+1)
      (advanceCandidateState (probePostState a out W rows (h depth.val) candidate)) := by
  let b := probePostState a out W rows (h depth.val) candidate
  have hw := SignatureRescanBridge.probe_preserves_cursor a out W rows (h depth.val) candidate
    ready ha.toCursorWords
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter)=false := by
    rw [ha.toCursorWords.available]
    simp only [Nat.ne_of_lt candidate.isLt,decide_false]
  have hf := SignatureRescanBridge.probe_control_flags a out W rows (h depth.val) candidate hzero
  have frame (i : Fin 896) (hk : i≠rescanStacks 17) (hl : i≠rescanStacks 22) : b.stacks i=a.stacks i :=
    SignatureRescanBridge.probe_stack_frame a out W rows (h depth.val) candidate ready
      ha.decrementScratch i hk hl
  have hb : AncestorStorage h key levels base depth.val ancestors b := by
    refine ⟨ha.depth_le,?_,?_,?_,?_,hf.1.trans ha.active⟩
    · exact (frame _ (by decide) (by decide)).trans ha.cursors
    · exact (frame _ (by decide) (by decide)).trans ha.representatives
    · exact (frame _ (by decide) (by decide)).trans ha.heads
    · exact (frame _ (by decide) (by decide)).trans ha.address
  exact advance_scan_storage h key levels base depth ancestors candidate.val b hb hw candidate.isLt
    (hf.2.1.trans ha.leaf) ((frame _ (by decide) (by decide)).trans ha.payload)
    ((frame _ (by decide) (by decide)).trans ha.predecessor)

/-- The complete losing-candidate event uses the actual full-key scanner.
The returned iteration, semantic cursor, fixed retained cap and all-prefix
storage refer to one and the same execution. -/
theorem duplicate_step_oai (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r)
    (ancestors : Prefix (Representatives s.key) depth.val)
    (candidate : Fin (2^s.headSize depth.val)) (a : State 40 896)
    (ha : ScanBoundary s F depth ancestors candidate.val a)
    (hdup : ¬ ∀ j, j < candidate → s.key depth.val j ≠ s.key depth.val candidate) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      ScanBoundary s F depth ancestors (candidate.val+1) b ∧
      n+1 ≤ (candidate.val+1)*eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i : Fin 896,i≠838 → i≠843 → i≠362 → b.stacks i=a.stacks i := by
  obtain ⟨raw,shifted,hr,hy,hready⟩ := ha.matrix.data
  have ready := hready candidate.isLt
  let C := 3*(s.input.columnLength+s.bound)+1
  have hshape := shifted_rows_bounds s.input (s.base+depth.val) s.bound
    (s.source.stacks 141) raw shifted (s.bounded 141) hr hy
  have hbud := scanner_caps_polynomial s.input s.source s.bound (s.base+depth.val)
    s.ready s.bounded (s.source.stacks 141) (s.bounded 141) raw shifted hr hy
  have hkernel := scan_kernel s depth.val raw shifted hr hy
  have hactual := (actual_duplicate_iff_model _ _ hkernel candidate).mpr hdup
  obtain ⟨n,out,he,hbound,hprefix,ht⟩ := duplicate_run_space loadHead visit a
    (s.source.stacks 141) shifted (s.headSize depth.val) C F candidate ready
    ha.toCursorWords hshape.2.1 hshape.2.2 ha.leaf hactual ha.bound cap.positive
    ((Nat.add_le_add_right (s.headSize_le depth.val) 1).trans cap.cursor)
    (hbud.2.2.trans cap.scanner) (hbud.2.1.trans cap.scanner)
  let b := advanceCandidateState (probePostState a out (s.source.stacks 141) shifted
    (s.headSize depth.val) candidate)
  have hb : ScanBoundary s F depth ancestors (candidate.val+1) b := by
    refine ⟨probe_advance_storage s.headSize s.key s.input.r s.base depth ancestors candidate a out
      (s.source.stacks 141) shifted ha.toScanStorage ready,hbound,
      duplicate_masters s a out (s.source.stacks 141) shifted (s.headSize depth.val)
        candidate ready ha.toCursorWords ha.masters,?_,?_⟩
    · constructor
      refine ⟨raw,shifted,hr,hy,?_⟩
      intro hc
      exact probe_advance_ready a out (s.source.stacks 141) shifted (s.headSize depth.val)
        candidate ⟨candidate.val+1,hc⟩ rfl ready ha.toCursorWords
    · exact (duplicate_stack_frame a out (s.source.stacks 141) shifted (s.headSize depth.val)
        candidate ready ha.toCursorWords 649 (by decide) (by decide) (by decide)).trans ha.address649
  refine ⟨n,b,SignatureTupleBranchSpace.iteration_of_eval he,hb,?_,?_,?_⟩
  · apply ht.trans
    apply Nat.mul_le_mul_left
    have hp : AttainedSignatureProgram.Rescan.polynomialBudget (s.source.stacks 141)
        shifted (s.headSize depth.val) C ≤ scannerEnvelope s.bound := hbud.1
    unfold eventPolynomial
    omega
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by unfold prefixEnvelope; omega)
  · intro i hc hr hf
    exact duplicate_stack_frame a out (s.source.stacks 141) shifted (s.headSize depth.val)
      candidate ready ha.toCursorWords i hc hr hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.duplicate_step_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.duplicate_step_oai
