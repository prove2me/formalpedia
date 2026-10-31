-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:28:30.099539+00:00
-- url     : https://prove2.me/submissions/bce1ca5f-0f1e-44dd-8325-451b983ecf90

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram_Selector_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem bits_value (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp []
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      cases b <;> simp [BinaryArithmetic.toNat, ih, Nat.bit, Nat.add_comm]

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Sunflower
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The elementary sunflower bound and its literal-occurrence corollary. -/
namespace SubexponentialSAT.Sunflower

open Finset
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Distinct unit sets give the separately specified bound `L₁ = 1`. -/
theorem unit_literal_occurrence_le (F : Finset (Finset α)) (x : α) :
    (F.filter (fun s => s.card = 1 ∧ x ∈ s)).card ≤ 1 := by
  have hsub : F.filter (fun s => s.card = 1 ∧ x ∈ s) ⊆ {{x}} := by
    intro s hs
    obtain ⟨_, hcard, hx⟩ := mem_filter.mp hs
    apply mem_singleton.mpr
    obtain ⟨y, rfl⟩ := card_eq_one.mp hcard
    have hxy : x = y := mem_singleton.mp hx
    rw [hxy]
  simpa using card_le_card hsub


/-- Summing the width-specific degrees bounds the total degree of one literal. -/
theorem literal_total_occurrence_le (F : Finset (Finset α)) (k : ℕ)
    (b : ℕ → ℕ) (x : α) (hWidth : ∀ s ∈ F, s.card ≤ k)
    (hBound : ∀ j, j ≤ k →
      (F.filter (fun s => s.card = j ∧ x ∈ s)).card ≤ b j) :
    (F.filter (fun s => x ∈ s)).card ≤ ∑ j ∈ range (k + 1), b j := by
  have hsub : F.filter (fun s => x ∈ s) ⊆
      (range (k + 1)).biUnion (fun j => F.filter (fun s => s.card = j ∧ x ∈ s)) := by
    intro s hs
    obtain ⟨hsF, hxs⟩ := mem_filter.mp hs
    apply mem_biUnion.mpr
    refine ⟨s.card, mem_range.mpr ?_, mem_filter.mpr ⟨hsF, rfl, hxs⟩⟩
    have := hWidth s hsF
    omega
  calc
    (F.filter (fun s => x ∈ s)).card ≤
        ((range (k + 1)).biUnion
          (fun j => F.filter (fun s => s.card = j ∧ x ∈ s))).card := card_le_card hsub
    _ ≤ ∑ j ∈ range (k + 1), (F.filter (fun s => s.card = j ∧ x ∈ s)).card :=
      card_biUnion_le
    _ ≤ ∑ j ∈ range (k + 1), b j := by
      apply sum_le_sum
      intro j hj
      exact hBound j (by have := mem_range.mp hj; omega)

/-- A variable has two signs, so a common literal-degree cap gives twice that cap
for the number of clauses containing the variable. -/
theorem variable_occurrence_le_of_literal_bound {V : Type*} [DecidableEq V]
    (F : SAT.CNF V) (B : ℕ)
    (hBound : ∀ x : SAT.Literal V, (F.filter (fun s => x ∈ s)).card ≤ B) :
    SAT.OccurrenceAtMost (2 * B) F := by
  intro v
  let pos : SAT.Literal V := ⟨v, true⟩
  let neg : SAT.Literal V := ⟨v, false⟩
  have hsub : F.filter (fun C => ∃ l ∈ C, l.variable = v) ⊆
      (F.filter (fun C => pos ∈ C)) ∪ (F.filter (fun C => neg ∈ C)) := by
    intro C hC
    obtain ⟨hCF, l, hl, hv⟩ := mem_filter.mp hC
    rcases l with ⟨w, sign⟩
    change w = v at hv
    subst w
    cases sign with
    | false => exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hCF, hl⟩))
    | true => exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hCF, hl⟩))
  calc
    SAT.occurrences v F ≤
        ((F.filter (fun C => pos ∈ C)) ∪ (F.filter (fun C => neg ∈ C))).card :=
      card_le_card hsub
    _ ≤ (F.filter (fun C => pos ∈ C)).card +
        (F.filter (fun C => neg ∈ C)).card := card_union_le _ _
    _ ≤ B + B := Nat.add_le_add (hBound pos) (hBound neg)
    _ = 2 * B := by omega

end SubexponentialSAT.Sunflower

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

open BitProgram StructuredCalls

theorem contains_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (x : α) (xs : List α) :
    ExecCNF.contains (f x) (xs.map f) = ExecCNF.contains x xs := by
  apply Bool.eq_iff_iff.mpr
  simp only [ExecCNF.contains_true, List.mem_map]
  constructor
  · rintro ⟨a, ha, heq⟩
    exact hf heq ▸ ha
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem subset_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (source target : List α) :
    ExecCNF.subset (source.map f) (target.map f) = ExecCNF.subset source target := by
  induction source with
  | nil => rfl
  | cons x xs ih => simp [ExecCNF.subset, contains_map_injective f hf, ih]

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CNFNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Raw input normalization for the frozen counting manuscript, lines 1758–1762.
The ambient type remains `Fin n` throughout, including unused variables.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

variable {n : ℕ}

theorem formulaSet_width_le (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) : SAT.WidthAtMost k (ExecCNF.formulaSet F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  exact D.toFinset_card_le.trans (h D hD)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriority
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: smallest-width, largest-core selection and marked degrees. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority

open OAI.Algorithms.SubexponentialSAT.SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

theorem select_spec {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (h : select F M = some (c, H)) :
    (∃ C ∈ F, C.card = c ∧ H ⊆ C) ∧ 0 < H.card ∧ H.card < c ∧
      M ^ (c - H.card) ≤ degree F c H := by
  have hm : (c, H) ∈ select F M := by simp [h]
  exact (mem_violatingCandidates F M c H).mp (List.argmin_mem hm)

private theorem mem_violating_of_degree {F : CNF (Fin n)} {M c : ℕ}
    {H : Clause (Fin n)} (hM : 0 < M) (hH : 0 < H.card) (hc : H.card < c)
    (hd : M ^ (c - H.card) ≤ degree F c H) :
    (c, H) ∈ violatingCandidates F M := by
  apply (mem_violatingCandidates F M c H).mpr
  have hpos : 0 < (selected F c H).card := lt_of_lt_of_le (pow_pos hM _) hd
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
  exact ⟨⟨C, (mem_selected.mp hC).1, (mem_selected.mp hC).2⟩, hH, hc, hd⟩

theorem select_none_degree_lt {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (hM : 0 < M) (h : select F M = none) (hH : 0 < H.card) (hc : H.card < c) :
    degree F c H < M ^ (c - H.card) := by
  by_contra hnot
  have hm := mem_violating_of_degree hM hH hc (Nat.le_of_not_gt hnot)
  have he : violatingCandidates F M = [] := List.argmin_eq_none.mp h
  simp [he] at hm


theorem select_eq_none_of_degrees {F : CNF (Fin n)} {M : ℕ}
    (h : ∀ (c : ℕ) (H : Clause (Fin n)), 0 < H.card → H.card < c →
      degree F c H < M ^ (c - H.card)) : select F M = none := by
  cases hs : select F M with
  | none => rfl
  | some p =>
    have hp := select_spec hs
    exact (Nat.not_lt_of_ge hp.2.2.2 (h p.1 p.2 hp.2.1 hp.2.2.1)).elim

@[simp] theorem select_empty (M : ℕ) : select (∅ : CNF (Fin n)) M = none := by
  cases h : select (∅ : CNF (Fin n)) M with
  | none => rfl
  | some p =>
    obtain ⟨C, hC, _⟩ := (select_spec h).1
    simp at hC

@[simp] theorem select_singleton_empty (M : ℕ) :
    select ({∅} : CNF (Fin n)) M = none := by
  cases h : select ({∅} : CNF (Fin n)) M with
  | none => rfl
  | some p =>
    obtain ⟨⟨C, hC, hwidth, _⟩, hnonempty, hproper, _⟩ := select_spec h
    have hC' : C = ∅ := Finset.mem_singleton.mp hC
    simp only [hC', Finset.card_empty] at hwidth
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sharp numerical budgets for disjoint counting sparsification

The frozen counting manuscript, Appendix A, lines 1991–2054. These numerical lemmas do not assert the
existence of a sparsification tree or a primitive implementation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget

open Finset
open scoped BigOperators

theorem sum_pow_le_twice_last (M : ℕ) (hM : 2 ≤ M) (j : ℕ) :
    ∑ i ∈ range (j + 1), M ^ i ≤ 2 * M ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ]
    have hp : 2 * M ^ j ≤ M ^ (j + 1) := by
      rw [pow_succ]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (M ^ j) hM
    omega

theorem occurrenceCap_le (k M : ℕ) (hk : 0 < k) (hM : 2 ≤ M) :
    occurrenceCap k M ≤ 4 * M ^ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h := sum_pow_le_twice_last M hM j
  dsimp [occurrenceCap]
  calc
    2 * ∑ i ∈ range (j + 1), M ^ i ≤ 2 * (2 * M ^ j) := Nat.mul_le_mul_left 2 h
    _ = 4 * M ^ (j + 1 - 1) := by simp; ring

open SparseCharging

/-- Terminality of the actual priority selector gives the sharp occurrence cap.
Unused variables contribute zero occurrences and are retained in the ambient type. -/
theorem leaf_occurrences_le {n : ℕ} (F : SAT.CNF (Fin n)) (k M : ℕ)
    (hM : 2 ≤ M) (hWidth : ∀ C ∈ F, C.card ≤ k)
    (hTerminal : SparsePriority.select F M = none) :
    ∀ v, SAT.occurrences v F ≤ occurrenceCap k M := by
  apply Sunflower.variable_occurrence_le_of_literal_bound F
    (∑ j ∈ range k, M ^ j)
  intro x
  calc
    (F.filter (fun C => x ∈ C)).card ≤
        ∑ j ∈ range (k + 1), if j = 0 then 0 else M ^ (j - 1) := by
      apply Sunflower.literal_total_occurrence_le F k _ x hWidth
      intro j _
      rcases j with _ | j
      · have hempty : F.filter (fun C => C.card = 0 ∧ x ∈ C) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro C hC
          obtain ⟨_, hc, hx⟩ := Finset.mem_filter.mp hC
          rw [Finset.card_eq_zero.mp hc] at hx
          simp at hx
        rw [hempty]
        simp
      · cases j with
        | zero => simpa using Sunflower.unit_literal_occurrence_le F x
        | succ j =>
          have hd := SparsePriority.select_none_degree_lt (F := F) (M := M)
            (c := j + 1 + 1) (H := {x}) (by omega) hTerminal (by simp) (by simp)
          simpa [SparsePriority.degree, DisjointBranch.selected] using hd.le
    _ = ∑ j ∈ range k, M ^ j := by rw [Finset.sum_range_succ']; simp

theorem leaf_occurrences_le_power {n : ℕ} (F : SAT.CNF (Fin n)) (k M : ℕ)
    (hk : 0 < k) (hM : 2 ≤ M) (hWidth : ∀ C ∈ F, C.card ≤ k)
    (hTerminal : SparsePriority.select F M = none) :
    ∀ v, SAT.occurrences v F ≤ 4 * M ^ (k - 1) := by
  intro v
  exact (leaf_occurrences_le F k M hM hWidth hTerminal v).trans (occurrenceCap_le k M hk hM)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- The final concrete halt instruction changes no stack and preserves the
bound already established through the command's exit boundary. -/
theorem compiled_halt_stack_bound {r s : ℕ} {command : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval command steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp
  by_cases hbefore : prefixSteps ≤ steps
  · exact hsource prefixSteps intermediate hbefore hp
  · have hlast : prefixSteps = steps + 1 := by omega
    subst prefixSteps
    have heq := trace_same_length_unique hp
      (StructuredCalls.compiled_halt_trace heval inputStack outputStack)
    rw [heq]
    have hend := hsource steps (b.withPC (some (StructuredCalls.exitAddress command))) le_rfl
      (StructuredCalls.compiled_trace heval inputStack outputStack)
    exact hend

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.EncodingLength

theorem length_perm {α : Type*} (enc : α → List Bool)
    {xs ys : List α} (h : xs.Perm ys) :
    (Encoding.encodeList enc xs).length = (Encoding.encodeList enc ys).length := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Encoding.length_encodeList_cons, ih]
  | swap a b xs => simp only [Encoding.length_encodeList_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem length_reverse {α : Type*} (enc : α → List Bool) (xs : List α) :
    (Encoding.encodeList enc xs.reverse).length = (Encoding.encodeList enc xs).length :=
  length_perm enc (List.reverse_perm xs)

theorem length_le_of_sublist {α : Type*} (enc : α → List Bool)
    {xs ys : List α} (h : xs.Sublist ys) :
    (Encoding.encodeList enc xs).length ≤ (Encoding.encodeList enc ys).length := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a h ih =>
      rw [Encoding.length_encodeList_cons]
      omega
  | cons_cons a h ih =>
      rw [Encoding.length_encodeList_cons, Encoding.length_encodeList_cons]
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.EncodingLength

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

theorem selectedRaw_set {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (c : ℕ) (H : List (SAT.Literal V))
    (hF : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (selectedRaw F c H) =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  ext D
  simp only [ExecCNF.mem_formulaSet, DisjointBranch.mem_selected]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨hCF, htest⟩ := List.mem_filter.mp hC
    obtain ⟨hc, hsub⟩ := Bool.and_eq_true_iff.mp htest
    have hcard := List.toFinset_card_of_nodup (hF C hCF)
    exact ⟨⟨C, hCF, rfl⟩, hcard.trans (of_decide_eq_true hc),
      (ExecCNF.subset_true H C).mp hsub⟩
  · rintro ⟨⟨C, hCF, rfl⟩, hc, hsub⟩
    refine ⟨C, List.mem_filter.mpr ⟨hCF, ?_⟩, rfl⟩
    apply Bool.and_eq_true_iff.mpr
    have hcard := List.toFinset_card_of_nodup (hF C hCF)
    exact ⟨decide_eq_true (hcard.symm.trans hc), (ExecCNF.subset_true H C).mpr hsub⟩

theorem selectedRaw_length {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (c : ℕ) (H : List (SAT.Literal V))
    (hF : ∀ C ∈ F, C.Nodup) (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    (selectedRaw F c H).length =
      SparsePriority.degree (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  have hn : ((selectedRaw F c H).map ExecCNF.clauseSet).Nodup :=
    (List.Sublist.map ExecCNF.clauseSet List.filter_sublist).nodup hdistinct
  have hc := List.toFinset_card_of_nodup hn
  change (ExecCNF.formulaSet (selectedRaw F c H)).card = _ at hc
  rw [selectedRaw_set F c H hF, List.length_map] at hc
  exact hc.symm

theorem selectedRaw_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (F : List (List α)) (c : ℕ) (H : List α) :
    selectedRaw (F.map (List.map f)) c (H.map f) = (selectedRaw F c H).map (List.map f) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    cases h : decide (C.length = c) && ExecCNF.subset H C <;>
      simp [selectedRaw, List.length_map,
        ExecClauseRelationsProgram.subset_map_injective f hf, h] at ih ⊢
    all_goals exact ih

theorem masked_sublist {α : Type*} (mask : List Bool) (C : List α) :
    (masked mask C).Sublist C := by
  induction C generalizing mask with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [masked]
    split
    · exact .cons_cons x (ih mask.tail)
    · exact .cons x (ih mask.tail)

theorem masked_map {α β : Type*} (f : α → β) (mask : List Bool) (C : List α) :
    masked mask (C.map f) = (masked mask C).map f := by
  induction C generalizing mask with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, masked]; split <;> simp [ih]

theorem masked_membership {α : Type*} [DecidableEq α] (C : List α) (H : Finset α)
    (suffix : List Bool) :
    masked (C.map (fun x => decide (x ∈ H)) ++ suffix) C = C.filter (fun x => decide (x ∈ H)) := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ H <;> simp [masked, hx, ih]

theorem exists_masked {α : Type*} [DecidableEq α] (k : ℕ) (C : List α) (H : Finset α)
    (hC : C.length ≤ k) (hH : H ⊆ C.toFinset) :
    ∃ mask ∈ masks k, (masked mask C).toFinset = H := by
  let mask := C.map (fun x => decide (x ∈ H)) ++ List.replicate (k - C.length) false
  refine ⟨mask, (mem_masks mask k).mpr ?_, ?_⟩
  · simp [mask, Nat.add_sub_of_le hC]
  · rw [show masked mask C = C.filter (fun x => decide (x ∈ H)) from masked_membership C H _]
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨by simpa using hH h, h⟩⟩

theorem rawCandidates_complete {α : Type*} [DecidableEq α]
    (k : ℕ) (F : List (List α)) (C : List α) (H : Finset α)
    (hC : C ∈ F) (hwidth : C.length ≤ k) (hH : H ⊆ C.toFinset) :
    ∃ core, (C.length, core) ∈ rawCandidates k F ∧ core.toFinset = H ∧ core.Sublist C := by
  obtain ⟨mask, hm, he⟩ := exists_masked k C H hwidth hH
  refine ⟨masked mask C, ?_, he, masked_sublist mask C⟩
  exact List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨mask, hm, rfl⟩⟩

theorem rawCandidate_spec {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, C.length = c ∧ H.Sublist C := by
  obtain ⟨C, hC, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, _, hp⟩ := List.mem_map.mp hm
  obtain ⟨hc, hH⟩ := Prod.mk.inj hp
  exact ⟨C, hC, hc, hH ▸ masked_sublist mask C⟩

theorem represent_core {n : ℕ} (k : ℕ) (F : List (List (SAT.Literal (Fin n))))
    (c : ℕ) (H : SAT.Clause (Fin n))
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdegree : 0 < SparsePriority.degree (ExecCNF.formulaSet F) c H) :
    ∃ core, (c, core) ∈ rawCandidates k F ∧ ExecCNF.clauseSet core = H ∧ core.length = H.card := by
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hdegree
  obtain ⟨hCF, hc, hH⟩ := DisjointBranch.mem_selected.mp hC
  obtain ⟨rawC, hrawC, rfl⟩ := ExecCNF.mem_formulaSet.mp hCF
  have hrawlen : rawC.length = c :=
    (List.toFinset_card_of_nodup (hnodup rawC hrawC)).symm.trans hc
  obtain ⟨core, hcore, he, hsub⟩ :=
    rawCandidates_complete k F rawC H hrawC (hwidth rawC hrawC) hH
  have hnodupCore := hsub.nodup (hnodup rawC hrawC)
  refine ⟨core, hrawlen ▸ hcore, he, ?_⟩
  exact (List.toFinset_card_of_nodup hnodupCore).symm.trans (congrArg Finset.card he)

/-- Source-level negative evidence obtained after every finite candidate fails. -/
theorem select_none_of_raw_failure {n : ℕ} (k : ℕ)
    (F : List (List (SAT.Literal (Fin n)))) (M : ℕ) (hM : 0 < M)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup)
    (hfail : ∀ c core, (c, core) ∈ rawCandidates k F → 0 < core.length → core.length < c →
      (selectedRaw F c core).length < M ^ (c - core.length)) :
    SparsePriority.select (ExecCNF.formulaSet F) M = none := by
  apply SparsePriority.select_eq_none_of_degrees
  intro c H hH hc
  by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) c H = 0
  · rw [hz]
    exact pow_pos hM _
  obtain ⟨core, hcore, he, hlen⟩ := represent_core k F c H hwidth hnodup (Nat.pos_of_ne_zero hz)
  have hf := hfail c core hcore (by omega) (by omega)
  simpa only [selectedRaw_length F c core hnodup hdistinct, he, hlen] using hf

theorem RawPriority.toPriority {n : ℕ} {k : ℕ} {F : List (List (SAT.Literal (Fin n)))}
    {M c : ℕ} {H : List (SAT.Literal (Fin n))} (h : RawPriority k F M c H) (hM : 0 < M)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    SparsePriority.Priority (ExecCNF.formulaSet F) M c (ExecCNF.clauseSet H) := by
  obtain ⟨C, hCF, hc, hsub⟩ := rawCandidate_spec k F c H h.candidate
  have hHnodup := hsub.nodup (hnodup C hCF)
  have hHcard : (ExecCNF.clauseSet H).card = H.length := List.toFinset_card_of_nodup hHnodup
  have hCcard : (ExecCNF.clauseSet C).card = c :=
    (List.toFinset_card_of_nodup (hnodup C hCF)).trans hc
  refine ⟨⟨ExecCNF.clauseSet C, ExecCNF.mem_formulaSet.mpr ⟨C, hCF, rfl⟩, hCcard, ?_⟩,
    hHcard.symm ▸ h.core_nonempty, hHcard.symm ▸ h.core_proper, ?_, ?_, ?_⟩
  · intro l hl
    exact ExecCNF.mem_clauseSet.mpr (hsub.subset (ExecCNF.mem_clauseSet.mp hl))
  · simpa only [hHcard, selectedRaw_length F c H hnodup hdistinct] using h.threshold
  · intro d S hS hSd hdc
    by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) d S = 0
    · rw [hz]; exact pow_pos hM _
    obtain ⟨core, hcore, he, hlen⟩ := represent_core k F d S hwidth hnodup (Nat.pos_of_ne_zero hz)
    have hf := h.minimum d core hcore (by omega) (by omega) hdc
    simpa only [selectedRaw_length F d core hnodup hdistinct, he, hlen] using hf
  · intro S hHS hSc
    by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) c S = 0
    · rw [hz]; exact pow_pos hM _
    obtain ⟨core, hcore, he, hlen⟩ := represent_core k F c S hwidth hnodup (Nat.pos_of_ne_zero hz)
    have hf := h.maximum core hcore (by omega) (by omega)
    simpa only [selectedRaw_length F c core hnodup hdistinct, he, hlen] using hf

namespace ThresholdPower

theorem runtime_polynomial (exponent : ℕ) (base : List Bool) :
    PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 3 ≤
      (100 * (exponent + 1) ^ 2 + 20 * (exponent + 1) * (exponent.bits.length + 1) + 6) *
        (base.length + 1) ^ 2 := by
  simp only [PowerPrograms.runtimeBound, PowerPrograms.workBound,
    PowerPrograms.callbackBound, ArithmeticExpressionSupport.bits_value]
  have hsq : 1 ≤ (base.length + 1) ^ 2 := one_le_pow₀ (by omega)
  have hinner : 2 + (exponent + 1) * base.length ≤
      2 * (exponent + 1) * (base.length + 1) := by
    ring_nf
    omega
  have hmain := Nat.mul_le_mul_left (exponent * (50 * (base.length + 1))) hinner
  have hexp : exponent ≤ exponent + 1 := by omega
  have hmain' := Nat.mul_le_mul_right
    (100 * (exponent + 1) * (base.length + 1) ^ 2) hexp
  have htail : (exponent + 1) * (16 * exponent.bits.length + 16) +
      4 * exponent.bits.length + 6 ≤
      20 * (exponent + 1) * (exponent.bits.length + 1) + 6 := by
    ring_nf
    omega
  have hprod := Nat.mul_le_mul_left
    (20 * (exponent + 1) * (exponent.bits.length + 1) + 6) hsq
  nlinarith only [hmain, hmain', htail, hprod]

end ThresholdPower

namespace Selector

theorem formulaCode_selectedFamily_length_le (F : Formula) (H : Clause) (width : List Bool) :
    (Filter.formulaCode (selectedFamily F H width)).length ≤ (Filter.formulaCode F).length := by
  unfold selectedFamily Filter.formulaCode
  rw [EncodingLength.length_reverse]
  exact EncodingLength.length_le_of_sublist Filter.clauseCode List.filter_sublist

theorem rawCandidate_witness {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, ∃ mask, mask.length = k ∧ C.length = c ∧ masked mask C = H := by
  obtain ⟨C, hCF, hC⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, hm, heq⟩ := List.mem_map.mp hC
  obtain ⟨hc, hH⟩ := Prod.mk.inj heq
  exact ⟨C, hCF, mask, (mem_masks mask k).mp hm, hc, hH⟩

theorem rawCandidate_map {α β : Type*} (f : α → β) (k : ℕ) (F : List (List α))
    (c : ℕ) (H : List α) (hraw : (c, H) ∈ rawCandidates k F) :
    (c, H.map f) ∈ rawCandidates k (F.map (List.map f)) := by
  obtain ⟨C, hCF, mask, hm, hc, hH⟩ := rawCandidate_witness k F c H hraw
  apply List.mem_flatMap.mpr
  refine ⟨C.map f, List.mem_map.mpr ⟨C, hCF, rfl⟩,
    List.mem_map.mpr ⟨mask, (mem_masks mask k).mpr hm, ?_⟩⟩
  simp [List.length_map, hc, masked_map, hH]

theorem rawPriority_of_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (k : ℕ) (F : List (List α)) (M c : ℕ)
    (word : List β) (priority : RawPriority k (F.map (List.map f)) M c word) :
    ∃ H : List α, H.map f = word ∧ RawPriority k F M c H := by
  obtain ⟨Cword, hCF, mask, hm, hc, hH⟩ :=
    rawCandidate_witness k (F.map (List.map f)) c word priority.candidate
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hCF
  let H := masked mask C
  have hmap : H.map f = word := by simpa only [masked_map] using hH
  have hlen : H.length = word.length := by rw [← hmap, List.length_map]
  have hclen : C.length = c := by simpa only [List.length_map] using hc
  refine ⟨H, hmap, ?_⟩
  constructor
  · apply List.mem_flatMap.mpr
    exact ⟨C, hC, List.mem_map.mpr ⟨mask, (mem_masks mask k).mpr hm, by simp [hclen, H]⟩⟩
  · simpa only [hlen] using priority.core_nonempty
  · simpa only [hlen] using priority.core_proper
  · have ht := priority.threshold
    rw [← hmap, List.length_map, selectedRaw_map f hf, List.length_map] at ht
    exact ht
  · intro d core hraw hpos hproper hdc
    have hh := priority.minimum d (core.map f) (rawCandidate_map f k F d core hraw)
      (by simpa only [List.length_map] using hpos)
      (by simpa only [List.length_map] using hproper) hdc
    simpa only [List.length_map, selectedRaw_map f hf] using hh
  · intro core hraw hlarge hproper
    have hh := priority.maximum (core.map f) (rawCandidate_map f k F c core hraw)
      (by simpa only [List.length_map, ← hlen] using hlarge)
      (by simpa only [List.length_map] using hproper)
    simpa only [List.length_map, selectedRaw_map f hf] using hh

theorem widthFamily_code_length_le (F : Formula) (width : List Bool) :
    (Filter.formulaCode (widthFamily F width)).length ≤ (Filter.formulaCode F).length :=
  formulaCode_selectedFamily_length_le F [] width

theorem familyInitBound_le (F : Formula) (width : List Bool) :
    familyInitBound F width ≤ 1000 * ((Filter.formulaCode F).length + width.length + 2) ^ 3 := by
  let L := (Filter.formulaCode F).length + width.length + 2
  have hf := widthFamily_code_length_le F width
  have hlin : L ≤ L ^ 3 := Nat.le_self_pow (by decide) L
  have hL : 1 ≤ L ^ 3 := by apply one_le_pow₀; dsimp [L]; omega
  change _ ≤ 1000 * L ^ 3
  unfold familyInitBound
  change 3 + (2 * width.length + 1) + (7 * (Filter.formulaCode F).length + 5) +
    (600 * L ^ 3 + 3) + 5 + (6 * (Filter.formulaCode (widthFamily F width)).length + 6) ≤ _
  have hF : (Filter.formulaCode F).length ≤ L := by dsimp [L]; omega
  have hW : width.length ≤ L := by dsimp [L]; omega
  have hF3 := hF.trans hlin
  have hW3 := hW.trans hlin
  omega

theorem parameterInitBound_le (F : Formula) (base size : List Bool) (c exponent : ℕ) :
    parameterInitBound exponent size base (Filter.formulaCode (widthFamily F c.bits)) ≤
      (powerCoefficient exponent + 2 * size.length + 14) * inputVolume F base ^ 2 := by
  let V := inputVolume F base
  have hp := ThresholdPower.runtime_polynomial exponent base
  change PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 3 ≤
    powerCoefficient exponent * (base.length + 1) ^ 2 at hp
  have hb : base.length + 1 ≤ V := by dsimp [V, inputVolume]; omega
  have hp' := hp.trans (Nat.mul_le_mul_left (powerCoefficient exponent) (Nat.pow_le_pow_left hb 2))
  have hV : 1 ≤ V := by dsimp [V, inputVolume]; omega
  have hV2 : 1 ≤ V ^ 2 := one_le_pow₀ hV
  have hlin : V ≤ V ^ 2 := Nat.le_self_pow (by decide) V
  have hf := widthFamily_code_length_le F c.bits
  have hfamily : (Filter.formulaCode (widthFamily F c.bits)).length ≤ V ^ 2 := by
    have hF : (Filter.formulaCode F).length ≤ V := by dsimp [V, inputVolume]; omega
    exact hf.trans (hF.trans hlin)
  have hconst := Nat.mul_le_mul_left (2 * size.length + 7) hV2
  unfold parameterInitBound
  change _ ≤ (powerCoefficient exponent + 2 * size.length + 14) * V ^ 2
  nlinarith only [hp', hfamily, hconst]

theorem phaseVolume_le (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool) :
    phaseVolume F base c h mask ≤ phaseScale c h mask * inputVolume F base := by
  let V := inputVolume F base
  have hV : 1 ≤ V := by dsimp [V, inputVolume]; omega
  have hF : (Filter.formulaCode F).length ≤ V := by dsimp [V, inputVolume]; omega
  have hb : base.length ≤ V := by dsimp [V, inputVolume]; omega
  have hf := widthFamily_code_length_le F c.bits
  have hprod := Nat.mul_le_mul_left (c - h) hb
  have hc := Nat.mul_le_mul_left (mask.length + c.bits.length + h.bits.length + 2) hV
  unfold phaseVolume phaseScale
  change _ ≤ (2 + mask.length + c.bits.length + h.bits.length + (c - h) + 2) * V
  nlinarith only [hF, hf, hprod, hc]

theorem phaseBound_polynomial (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool) :
    phaseBound F base c h mask ≤ phaseCoefficient c h mask * inputVolume F base ^ 4 := by
  let V := inputVolume F base
  have hV : 1 ≤ V := by dsimp [V, inputVolume]; omega
  have hV4 : 1 ≤ V ^ 4 := one_le_pow₀ hV
  have hlin : V ≤ V ^ 4 := Nat.le_self_pow (by decide) V
  have hsq : V ^ 2 ≤ V ^ 4 := pow_le_pow_right₀ hV (by decide)
  have hcube : V ^ 3 ≤ V ^ 4 := pow_le_pow_right₀ hV (by decide)
  have hsize : (Filter.formulaCode F).length + c.bits.length + 2 ≤ (c.bits.length + 2) * V := by
    have hvf : (Filter.formulaCode F).length + 1 ≤ V := by dsimp [V, inputVolume]; omega
    have hh := Nat.mul_le_mul_left (c.bits.length + 1) hV
    nlinarith only [hvf, hh]
  have hf := (familyInitBound_le F c.bits).trans
    (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hsize 3))
  rw [mul_pow, ← Nat.mul_assoc] at hf
  have hf' := hf.trans (Nat.mul_le_mul_left (1000 * (c.bits.length + 2) ^ 3) hcube)
  have hp := (parameterInitBound_le F base h.bits c (c - h)).trans
    (Nat.mul_le_mul_left (powerCoefficient (c - h) + 2 * h.bits.length + 14) hsq)
  have hv := phaseVolume_le F base c h mask
  have hv4 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left hv 4)
  rw [mul_pow, ← Nat.mul_assoc] at hv4
  have hclean := Nat.mul_le_mul_left (10 * phaseScale c h mask) hlin
  have hconst := Nat.mul_le_mul_left 15 hV4
  unfold phaseBound phaseCoefficient
  change _ ≤ (1000 * (c.bits.length + 2) ^ 3 +
    (powerCoefficient (c - h) + 2 * h.bits.length + 14) +
    3000 * phaseScale c h mask ^ 4 + (10 * phaseScale c h mask + 15)) * V ^ 4
  nlinarith only [hf', hp, hv4, hv, hclean, hconst]

theorem chainBudget_polynomial (F : Formula) (base : List Bool) (ps : List (ℕ × ℕ × List Bool)) :
    chainBudget F base ps ≤
      ((ps.map fun p => phaseCoefficient p.1 p.2.1 p.2.2).sum + 2 * ps.length) *
        inputVolume F base ^ 4 := by
  have hV : 1 ≤ inputVolume F base ^ 4 := by
    apply one_le_pow₀
    unfold inputVolume
    omega
  induction ps with
  | nil => simp [chainBudget]
  | cons p ps ih =>
    have hp := phaseBound_polynomial F base p.1 p.2.1 p.2.2
    simp only [chainBudget, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith only [ih, hp, hV]

theorem commandBound_polynomial (k : ℕ) (F : Formula) (base : List Bool) :
    1 + chainBudget F base (passes k) ≤ selectorCoefficient k * inputVolume F base ^ 4 := by
  have hc := chainBudget_polynomial F base (passes k)
  have hV : 1 ≤ inputVolume F base ^ 4 := by
    apply one_le_pow₀
    unfold inputVolume
    omega
  unfold selectorCoefficient
  nlinarith only [hc, hV]

theorem Boundary.stack_length_le (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) (i : Fin 24) : (d.stacks i).length ≤ inputVolume F base := by
  by_cases hi13 : i = 13
  · subst i; rw [hd.formula_word]; unfold inputVolume; omega
  by_cases hi19 : i = 19
  · subst i; rw [hd.parameter_word]; unfold inputVolume; omega
  rw [hd.scratch i hi13 hi19]
  simp

theorem Boundary.dataBits_le (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) {l : ℕ} (pc : Option (Fin l)) :
    dataBits (d.withPC pc) ≤ 24 * inputVolume F base := by
  unfold dataBits
  calc
    _ ≤ ∑ _ : Fin 24, inputVolume F base := by
      apply Finset.sum_le_sum
      intro i _
      exact hd.stack_length_le F base d i
    _ = _ := by simp

theorem command_execution (k : ℕ) (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∃ t ≤ selectorCoefficient k * inputVolume F base ^ 4, ∃ e : Data,
      Eval (command k) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧
        ∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H, RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = Filter.clauseCode H ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F c H)) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (program k) prefixSteps (d.withPC (some (program k).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          (selectorCoefficient k + 24) * inputVolume F base ^ 4) := by
  obtain ⟨t, ht, e, he, hframe, hmiss, hhit⟩ := command_eval k F base d hd hwidth
  have ht' := ht.trans (commandBound_polynomial k F base)
  refine ⟨t, ht', e, he, hframe, hmiss, hhit, ?_⟩
  intro prefixSteps intermediate hprefix htrace i
  have hl := StructuredSpace.local_stack_bound (program k)
    (steps := t) (hd.dataBits_le F base d (some (program k).entry))
    prefixSteps intermediate hprefix htrace i
  have hV : inputVolume F base ≤ inputVolume F base ^ 4 := Nat.le_self_pow (by decide) _
  nlinarith only [hl, ht', hV]

theorem command_execution_map {α : Type*} [DecidableEq α]
    (f : α → List Bool) (hf : Function.Injective f) (k : ℕ) (F : List (List α))
    (base : List Bool) (d : Data)
    (hd : Boundary (F.map (List.map f)) base d) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∃ t ≤ selectorCoefficient k * inputVolume (F.map (List.map f)) base ^ 4, ∃ e : Data,
      Eval (command k) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧
        ∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H, RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = Filter.clauseCode (H.map f) ∧
        e.stacks 12 = Filter.formulaCode ((selectedRaw F c H).map (List.map f))) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (program k) prefixSteps (d.withPC (some (program k).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          (selectorCoefficient k + 24) * inputVolume (F.map (List.map f)) base ^ 4) := by
  have hw : ∀ C ∈ F.map (List.map f), C.length ≤ k := by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    simpa only [List.length_map] using hwidth D hD
  obtain ⟨t, ht, e, he, hframe, hmiss, hhit, hspace⟩ :=
    command_execution k (F.map (List.map f)) base d hd hw
  refine ⟨t, ht, e, he, hframe, ?_, ?_, hspace⟩
  · intro hfalse
    obtain ⟨hs, hfails⟩ := hmiss hfalse
    refine ⟨hs, ?_⟩
    intro c H hraw hpos hproper
    have hh := hfails c (H.map f) (rawCandidate_map f k F c H hraw)
      (by simpa only [List.length_map] using hpos)
      (by simpa only [List.length_map] using hproper)
    simpa only [selectedRaw_map f hf, List.length_map] using hh
  · intro htrue
    obtain ⟨c, word, hpriority, h9, h12⟩ := hhit htrue
    obtain ⟨H, hH, hpriority'⟩ := rawPriority_of_map f hf k F (BinaryArithmetic.toNat base) c word hpriority
    refine ⟨c, H, hpriority', ?_, ?_⟩
    · simpa only [hH] using h9
    · simpa only [← hH, selectedRaw_map f hf] using h12

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSResource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Resource bounds for the actual outer DFS commands.

Cleanup is structurally nonallocating. The bounds below concern the concrete
finite tables and every source prefix, before applying the guarded primitive
compiler. The selector and leaf contracts still require their own executions.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource

open BitProgram StructuredCalls SparseDFSProgram

private theorem lifted_call_space {r s l steps localBound frameBound : ℕ}
    (routine : Program r s l) (register : Fin r ↪ Fin 80) (stack : Fin s ↪ Fin 1220)
    (frame : Data) {a b : State r s}
    (htrace : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hlocal : ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) c →
      ∀ i, (c.stacks i).length ≤ localBound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        prefixSteps ((embedState register stack frame a).withPC
          (some (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ max localBound frameBound := by
  have hsource := StructuredSpace.liftProgram_stack_bound routine register stack
    (frame.withPC none) register.injective stack.injective htrace hlocal hframe
  have he := eval_call_lifted routine register stack frame register.injective stack.injective htrace
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (ProgramLinking.liftProgram routine register stack)
        (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        (siteAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (exitAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (compiled_site (.call (ProgramLinking.liftProgram routine register stack)) 256 256) ht
      simpa only [ProgramLinking.embedCfg, ProgramLinking.relocatePc, embedState,
        StructuredProgram.State.withPC, id_eq] using hsource


/-- The real selector runs in the frozen root bank. Its semantic hit/miss
results and all-prefix storage bound come from the same local execution;
the final return instruction is included before relocation into the root. -/
theorem selectCurrent_execution_space {α : Type*} [DecidableEq α]
    (encode : α → List Bool) (hinjective : Function.Injective encode)
    (k : ℕ) (F : List (List α)) (base : List Bool)
    (initialLocal : SparsePriorityProgram.Selector.Data) (frame : Data) (frameBound : ℕ)
    (hlocal : SparsePriorityProgram.Selector.Boundary (F.map (List.map encode)) base initialLocal)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∃ t ≤ SparsePriorityProgram.Selector.selectorCoefficient k *
        SparsePriorityProgram.Selector.inputVolume (F.map (List.map encode)) base ^ 4,
      ∃ e : SparsePriorityProgram.Selector.Data,
      Eval (selectCurrent k) (t + 1)
        (embedState (registers 24 (by decide)) selectorStack frame initialLocal)
        (embedState (registers 24 (by decide)) selectorStack frame e) ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = initialLocal.stacks i) ∧
      (e.regs 23 = false → e.stacks = initialLocal.stacks ∧
        ∀ c H, (c, H) ∈ SparsePriorityProgram.rawCandidates k F →
          0 < H.length → H.length < c →
          (SparsePriorityProgram.selectedRaw F c H).length <
            BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H,
        SparsePriorityProgram.RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = SparsePriorityProgram.Filter.clauseCode (H.map encode) ∧
        e.stacks 12 = SparsePriorityProgram.Filter.formulaCode
          ((SparsePriorityProgram.selectedRaw F c H).map (List.map encode))) ∧
      ∀ prefixSteps c, prefixSteps ≤ t + 1 →
        Trace (compiled (selectCurrent k) 256 256) prefixSteps
          ((embedState (registers 24 (by decide)) selectorStack frame initialLocal).withPC
            (some (compiled (selectCurrent k) 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          ((SparsePriorityProgram.Selector.selectorCoefficient k + 24) *
            SparsePriorityProgram.Selector.inputVolume (F.map (List.map encode)) base ^ 4)
          frameBound := by
  obtain ⟨t, ht, e, he, hpreserve, hmiss, hhit, hspace⟩ :=
    SparsePriorityProgram.Selector.command_execution_map encode hinjective k F base initialLocal hlocal hwidth
  have htrace := compiled_halt_trace he 13 12
  have hhaltSpace := StructuredSpace.compiled_halt_stack_bound he 13 12 hspace
  refine ⟨t, ht, e, eval_call_lifted (SparsePriorityProgram.Selector.program k)
    (registers 24 (by decide)) selectorStack frame (registers 24 (by decide)).injective
    selectorStack.injective htrace, hpreserve, hmiss, hhit, ?_⟩
  exact lifted_call_space (SparsePriorityProgram.Selector.program k)
    (registers 24 (by decide)) selectorStack frame htrace hhaltSpace hframe


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseSelectorRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual root selector call and its typed Appendix A certificates.
The success and terminal conclusions, return instruction, and every-prefix
storage estimate all describe the same concrete execution. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement

open BitProgram StructuredCalls SparseDFSProgram SparsePriorityProgram

variable {n : ℕ}

theorem literalWord_injective : Function.Injective (literalWord (n := n)) :=
  Encoding.encodeNat_injective.comp Encoding.literalCode_injective

theorem clause_words (H : List (SAT.Literal (Fin n))) :
    Filter.clauseCode (H.map literalWord) =
      ExecCoreChildProgram.clauseCode (H.map Encoding.literalCode) := by
  induction H with
  | nil => rfl
  | cons l H ih =>
    change true :: (Encoding.frame (literalWord l) ++ Filter.clauseCode (H.map literalWord)) =
      true :: (Encoding.frame (literalWord l) ++
        ExecCoreChildProgram.clauseCode (H.map Encoding.literalCode))
    rw [ih]

theorem body_words (F : RawCNF n) :
    Filter.formulaCode (F.map (List.map literalWord)) = SparseCountProgram.encodeBody F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    change true :: (Encoding.frame (Filter.clauseCode (C.map literalWord)) ++
        Filter.formulaCode (F.map (List.map literalWord))) =
      true :: (Encoding.frame (ExecCoreChildProgram.clauseCode (C.map Encoding.literalCode)) ++
        SparseCountProgram.encodeBody F)
    rw [clause_words, ih]

theorem inputVolume_eq (F : RawCNF n) (base : List Bool) :
    Selector.inputVolume (F.map (List.map literalWord)) base = inputVolume F base := by
  rw [Selector.inputVolume, body_words, inputVolume]

theorem projection_boundary (F : RawCNF n) (base : List Bool) (d : Data)
    (hF : d.stacks 265 = SparseCountProgram.encodeBody F) (hM : d.stacks 259 = base)
    (hclean : ∀ i : Fin 1220, i.val < 24 → d.stacks i = []) :
    Selector.Boundary (F.map (List.map literalWord)) base
      (projectState (registers 24 (by decide)) selectorStack d) := by
  constructor
  · change d.stacks 265 = _
    rw [hF, body_words]
  · exact hM
  · intro i hi13 hi19
    change d.stacks (selectorStack i) = []
    apply hclean
    have hports : ∀ j : Fin 24, j ≠ 13 → j ≠ 19 → (selectorStack j).val < 24 := by decide
    exact hports i hi13 hi19

/-- The actual root call preserves every physical stack except its two output
ports. A failed call restores those ports too and proves the sharp leaf cap. -/
theorem selectCurrent_execution_oai {k : ℕ} (F : RawCNF n) (base : List Bool)
    (d : Data) (frameBound : ℕ) (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat base)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup)
    (hF : d.stacks 265 = SparseCountProgram.encodeBody F) (hbase : d.stacks 259 = base)
    (hclean : ∀ i : Fin 1220, i.val < 24 → d.stacks i = [])
    (hbound : ∀ i, (d.stacks i).length ≤ frameBound) :
    ∃ t ≤ Selector.selectorCoefficient k * inputVolume F base ^ 4 + 1, ∃ e : Data,
      Eval (selectCurrent k) t d e ∧
      (∀ i : Fin 1220, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧ e.stacks 9 = [] ∧ e.stacks 12 = [] ∧
        SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat base) = none ∧
        (∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
        ∀ v, SAT.occurrences v (ExecCNF.formulaSet F) ≤
          4 * BinaryArithmetic.toNat base ^ (k - 1)) ∧
      (e.regs 23 = true → ∃ c H,
        RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        SparsePriority.Priority (ExecCNF.formulaSet F) (BinaryArithmetic.toNat base) c
          (ExecCNF.clauseSet H) ∧
        e.stacks 9 = ExecCoreChildProgram.clauseCode (H.map Encoding.literalCode) ∧
        e.stacks 12 = SparseCountProgram.encodeBody (selectedRaw F c H)) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (compiled (selectCurrent k) 256 256) prefixSteps
          (d.withPC (some (compiled (selectCurrent k) 256 256).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max ((Selector.selectorCoefficient k + 24) * inputVolume F base ^ 4) frameBound) := by
  let a := projectState (registers 24 (by decide)) selectorStack d
  have ha : Selector.Boundary (F.map (List.map literalWord)) base a :=
    projection_boundary F base d hF hbase hclean
  obtain ⟨t, ht, localFinal, he, hframe, hmiss, hhit, hspace⟩ :=
    SparseDFSResource.selectCurrent_execution_space literalWord literalWord_injective k F base
      a d frameBound ha hwidth hbound
  have hstart : embedState (registers 24 (by decide)) selectorStack d a = d :=
    embedState_project _ _ d (registers 24 (by decide)).injective selectorStack.injective
  rw [hstart] at he hspace
  rw [inputVolume_eq] at ht hspace
  let e := embedState (registers 24 (by decide)) selectorStack d localFinal
  have hflag : e.regs 23 = localFinal.regs 23 :=
    embedState_register (registers 24 (by decide)) selectorStack d localFinal
      (registers 24 (by decide)).injective 23
  have hstack (i : Fin 24) : e.stacks (selectorStack i) = localFinal.stacks i :=
    embedState_stack (registers 24 (by decide)) selectorStack d localFinal selectorStack.injective i
  have hstackFrame (i : Fin 1220) (hi : ¬ ∃ j, selectorStack j = i) : e.stacks i = d.stacks i :=
    embedState_stack_frame (registers 24 (by decide)) selectorStack d localFinal i hi
  have hphysical (i : Fin 1220) (hi9 : i ≠ 9) (hi12 : i ≠ 12) : e.stacks i = d.stacks i := by
    by_cases hi : ∃ j, selectorStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hstack]
      apply hframe j
      · intro h; subst j; exact hi9 rfl
      · intro h; subst j; exact hi12 rfl
    · exact hstackFrame i hi
  refine ⟨t + 1, by omega, e, he, hphysical, ?_, ?_, hspace⟩
  · intro hfalse
    obtain ⟨hs, hfails⟩ := hmiss (hflag.symm.trans hfalse)
    have hes : e.stacks = d.stacks := by
      funext i
      by_cases hi : ∃ j, selectorStack j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [hstack, hs]
        rfl
      · exact hstackFrame i hi
    have hnone := select_none_of_raw_failure k F (BinaryArithmetic.toNat base) (by omega)
      hwidth hnodup hdistinct hfails
    refine ⟨hes, by rw [hes]; exact hclean 9 (by decide),
      by rw [hes]; exact hclean 12 (by decide), hnone, hfails, ?_⟩
    exact SparseBudget.leaf_occurrences_le_power (ExecCNF.formulaSet F) k
      (BinaryArithmetic.toNat base) (by omega) hM (formulaSet_width_le F hwidth) hnone
  · intro htrue
    obtain ⟨c, H, hp, h9, h12⟩ := hhit (hflag.symm.trans htrue)
    refine ⟨c, H, hp, hp.toPriority (by omega) hwidth hnodup hdistinct, ?_, ?_⟩
    · exact ((hstack 9).trans h9).trans (clause_words H)
    · exact ((hstack 12).trans h12).trans (body_words (selectedRaw F c H))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution_oai
