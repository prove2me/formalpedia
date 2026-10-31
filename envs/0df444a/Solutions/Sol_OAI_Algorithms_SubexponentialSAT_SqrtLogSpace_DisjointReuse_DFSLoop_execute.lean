-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:22:10.99785+00:00
-- url     : https://prove2.me/submissions/a785422c-ffd5-41d4-a7c5-d17d65d0dbdc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SunflowerBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal-set sunflower branching

Concrete CNF children and their semantic union, together with the absorption
invariants used by the cumulative-insertion argument. Opposite polarities are
distinct literals; no variable-disjointness premise is used.
-/

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

namespace Sunflower
variable {d : ℕ}

private theorem union_singleton_eq_insert (F : CNF V) (C : Clause V) :
    F ∪ {C} = insert C F := by
  ext D
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  exact or_comm

end Sunflower
end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

theorem sdiff_injective_on {F : CNF V} {H : Clause V}
    (hcore : ∀ C ∈ F, H ⊆ C) : Set.InjOn (fun C => C \ H) F := by
  intro C hC D hD heq
  change C \ H = D \ H at heq
  calc
    C = H ∪ (C \ H) := (Finset.union_sdiff_of_subset (hcore C hC)).symm
    _ = H ∪ (D \ H) := congrArg (fun P => H ∪ P) heq
    _ = D := Finset.union_sdiff_of_subset (hcore D hD)

end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
open scoped BigOperators
universe u
variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
theorem literalMass_mono {F G : CNF V} (h : F ⊆ G) : literalMass F ≤ literalMass G :=
  Finset.sum_le_sum_of_subset h

theorem literalMass_absorb_le (F : CNF V) : literalMass (absorb F) ≤ literalMass F :=
  literalMass_mono (absorb_subset F)

theorem literalMass_union_le (F G : CNF V) :
    literalMass (F ∪ G) ≤ literalMass F + literalMass G := by
  calc
    literalMass (F ∪ G) ≤ literalMass (F ∪ G) + literalMass (F ∩ G) := Nat.le_add_right _ _
    _ = literalMass F + literalMass G := Finset.sum_union_inter

theorem literalMass_insert_le (F : CNF V) (C : Clause V) :
    literalMass (insert C F) ≤ literalMass F + C.card := by
  have heq : insert C F = F ∪ {C} := by
    ext D
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    exact or_comm
  rw [heq]
  simpa only [literalMass_singleton] using literalMass_union_le F {C}

theorem literalMass_sdiff {F S : CNF V} (h : S ⊆ F) :
    literalMass (F \ S) + literalMass S = literalMass F := Finset.sum_sdiff h

omit [DecidableEq V] in
theorem clause_card_le_literalMass {F : CNF V} {C : Clause V} (hC : C ∈ F) :
    C.card ≤ literalMass F := by
  have hsub : ({C} : CNF V) ⊆ F := Finset.singleton_subset_iff.mpr hC
  simpa only [literalMass_singleton] using literalMass_mono hsub

end SubexponentialSAT.SunflowerBranch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem formulaSet_filter (F : Formula α) (p : Clause α → Bool)
    (q : Finset α → Prop) [DecidablePred q]
    (hp : ∀ C, p C = true ↔ q (clauseSet C)) :
    formulaSet (F.filter p) = (formulaSet F).filter q := by
  ext C
  simp only [mem_formulaSet, Finset.mem_filter]
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hD, htest⟩ := List.mem_filter.mp hD
    exact ⟨⟨D, hD, rfl⟩, (hp D).mp htest⟩
  · rintro ⟨⟨D, hD, rfl⟩, hq⟩
    exact ⟨D, List.mem_filter.mpr ⟨hD, (hp D).mpr hq⟩, rfl⟩

@[simp] theorem formulaSet_removeTautologies (neg : α → α) (F : Formula α) :
    formulaSet (removeTautologies neg F) =
      (formulaSet F).filter (fun C => ¬ ∃ x ∈ C, neg x ∈ C) := by
  apply formulaSet_filter
  intro C
  simp only [not_true_iff, tautology_true]

@[simp] theorem formulaSet_absorb (F : Formula α) :
    formulaSet (absorb F) =
      (formulaSet F).filter (fun C => ¬ ∃ D ∈ formulaSet F, D ⊂ C) := by
  change formulaSet ((dedupClauses F).filter _) = _
  rw [formulaSet_filter (dedupClauses F) _
    (fun C => ¬ ∃ D ∈ formulaSet F, D ⊂ C)]
  · rw [formulaSet_dedupClauses]
  · intro C
    simp only [not_true_iff, any_strictSubset_true]

@[simp] theorem formulaSet_eraseClauses (F S : Formula α) :
    formulaSet (eraseClauses F S) = formulaSet F \ formulaSet S := by
  unfold eraseClauses
  rw [formulaSet_filter F _ (fun C => C ∉ formulaSet S)]
  · ext C
    simp
  · intro C
    simp only [not_true_iff, any_equivalent_true]

section SAT
variable {V : Type u} [DecidableEq V]

@[simp] theorem absorb_set (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (absorb F) = SubexponentialSAT.SAT.absorb (formulaSet F) := formulaSet_absorb F

@[simp] theorem normalize_set (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (normalize SubexponentialSAT.SAT.Literal.negate F) = SubexponentialSAT.SAT.normalize (formulaSet F) := by
  simp only [normalize, absorb_set, formulaSet_removeTautologies, formulaSet_cleanLiterals]
  rfl

end SAT
end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFCodeTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact list transport through literal codes

These equalities preserve clause order and the last-occurrence conventions.
They connect the encoded normalization programs to the typed executable CNF
operations, rather than identifying only their finite-set semantics.
-/

namespace SubexponentialSAT.ExecCNFCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

theorem petal_filter_set (C H : Clause α) :
    clauseSet (C.filter (fun x => !decide (x ∈ H))) = clauseSet C \ clauseSet H := by
  ext x
  simp [clauseSet]

theorem petal_family_set (G : Formula α) (H : Clause α) :
    formulaSet (G.map (fun C => C.filter (fun x => !decide (x ∈ H)))) =
      (formulaSet G).image (fun C => C \ clauseSet H) := by
  ext D
  constructor
  · intro hD
    obtain ⟨C, hC, he⟩ := mem_formulaSet.mp hD
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hC
    exact Finset.mem_image.mpr ⟨clauseSet A, mem_formulaSet.mpr ⟨A, hA, rfl⟩,
      (petal_filter_set A H).symm.trans he⟩
  · intro hD
    obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hD
    obtain ⟨A, hA, rfl⟩ := mem_formulaSet.mp hC
    exact mem_formulaSet.mpr ⟨A.filter (fun x => !decide (x ∈ H)),
      List.mem_map.mpr ⟨A, hA, rfl⟩, (petal_filter_set A H).trans he⟩

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


/-- Set semantics of the exact list output, valid even with reordered or
repeated literals and repeated clauses in any of the supplied lists. -/
theorem result_set {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) :
    ExecCNF.formulaSet (result F selected H) =
      (insert (ExecCNF.clauseSet H) (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected)).filter
        (fun C => ¬ ∃ D ∈ insert (ExecCNF.clauseSet H)
          (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected), D ⊂ C) := by
  simp only [result, ExecCNF.formulaSet_absorb, ExecCNF.formulaSet_cons,
    ExecCNF.formulaSet_eraseClauses]

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual construction of the petal child. The core, selected family, and
parent occupy the same three ports as the core-child program. -/
namespace SubexponentialSAT.ExecPetalChildProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

theorem petals_set {α : Type*} [DecidableEq α] (selected : List (List α)) (H : List α) :
    ExecCNF.formulaSet (petals selected H) =
      (ExecCNF.formulaSet selected).image (fun C => C \ ExecCNF.clauseSet H) :=
  ExecCNFCodeTransport.petal_family_set selected H

theorem result_set {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) :
    let P := (ExecCNF.formulaSet selected).image (fun C => C \ ExecCNF.clauseSet H)
    let G := P ∪ (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected)
    ExecCNF.formulaSet (result F selected H) = G.filter (fun C => ¬ ∃ D ∈ G, D ⊂ C) := by
  simp only [result, ExecCNF.formulaSet_absorb, ExecCNF.formulaSet_append,
    ExecCNF.formulaSet_eraseClauses, petals_set]

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsify
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: literal-core branching with disjoint exact-count children. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch

open OAI.Algorithms.SubexponentialSAT.SAT

universe u
variable {V : Type u} [DecidableEq V]

theorem sdiff_injOn_selected (F : CNF V) (c : ℕ) (H : Clause V) :
    Set.InjOn (fun C => C \ H) (selected F c H) :=
  SunflowerBranch.sdiff_injective_on fun _ hC => (mem_selected.mp hC).2.2

theorem petals_card (F : CNF V) (c : ℕ) (H : Clause V) :
    (petals F c H).card = (selected F c H).card :=
  Finset.card_image_of_injOn (sdiff_injOn_selected F c H)

open scoped BigOperators

theorem literalMass_selected (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.literalMass (selected F c H) = (selected F c H).card * c := by
  exact Finset.sum_const_nat fun _ hC => (mem_selected.mp hC).2.1

theorem literalMass_petals (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.literalMass (petals F c H) =
      (selected F c H).card * (c - H.card) := by
  rw [← petals_card]
  exact Finset.sum_const_nat fun _ hP => petal_card hP

theorem literalMass_negatedCoreUnits (H : Clause V) :
    SunflowerBranch.literalMass (negatedCoreUnits H) = H.card := by
  have hinj : Set.InjOn (fun l : Literal V => ({l.negate} : Clause V)) H := by
    intro l _ m _ heq
    have hneg := Finset.singleton_injective heq
    simpa only [Literal.negate_negate] using congrArg Literal.negate hneg
  unfold SunflowerBranch.literalMass negatedCoreUnits
  rw [Finset.sum_image hinj]
  simp

theorem literalMass_childA_lt {F : CNF V} {c : ℕ} {H : Clause V}
    (hsel : (selected F c H).Nonempty) (hproper : H.card < c) :
    SunflowerBranch.literalMass (childA F c H) < SunflowerBranch.literalMass F := by
  obtain ⟨C, hC⟩ := hsel
  have hlt : H.card < SunflowerBranch.literalMass (selected F c H) :=
    (Finset.card_lt_card (core_strict_subset hC hproper)).trans_le
      (SunflowerBranch.clause_card_le_literalMass hC)
  have habsorb := SunflowerBranch.literalMass_absorb_le (insert H (F \ selected F c H))
  have hinsert := SunflowerBranch.literalMass_insert_le (F \ selected F c H) H
  have hsplit := SunflowerBranch.literalMass_sdiff (selected_subset F c H)
  change SunflowerBranch.literalMass (childA F c H) ≤ _ at habsorb
  omega

theorem literalMass_childB_lt {F : CNF V} {c : ℕ} {H : Clause V}
    (hH : H.Nonempty) (hproper : H.card < c) (hsize : 2 ≤ (selected F c H).card) :
    SunflowerBranch.literalMass (childB F c H) < SunflowerBranch.literalMass F := by
  have hmul : H.card < (selected F c H).card * H.card := by
    simpa using Nat.mul_lt_mul_of_pos_right (show 1 < (selected F c H).card by omega)
      (Finset.card_pos.mpr hH)
  have hlt : SunflowerBranch.literalMass (petals F c H) +
      SunflowerBranch.literalMass (negatedCoreUnits H) <
      SunflowerBranch.literalMass (selected F c H) := by
    rw [literalMass_petals, literalMass_negatedCoreUnits, literalMass_selected]
    calc
      (selected F c H).card * (c - H.card) + H.card <
          (selected F c H).card * (c - H.card) + (selected F c H).card * H.card :=
        Nat.add_lt_add_left hmul _
      _ = (selected F c H).card * c := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hproper.le]
  have habsorb := SunflowerBranch.literalMass_absorb_le
    (((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H)
  have hunits := SunflowerBranch.literalMass_union_le
    ((F \ selected F c H) ∪ petals F c H) (negatedCoreUnits H)
  have hpetals := SunflowerBranch.literalMass_union_le (F \ selected F c H) (petals F c H)
  have hsplit := SunflowerBranch.literalMass_sdiff (selected_subset F c H)
  change SunflowerBranch.literalMass (childB F c H) ≤ _ at habsorb
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

theorem trace_suffix {α : Type*} {step : α → Option α}
    {c d intermediate : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps c d)
    (hp : Computation.Trace step prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) :
    Computation.Trace step (steps - prefixSteps) intermediate d := by
  apply Computation.Trace.of_iterate
  have h := tr.iterate
  conv_lhs at h => rw [← Nat.sub_add_cancel hle]
  rw [Function.iterate_add_apply, hp.iterate] at h
  exact h

theorem trace_prefix_bound_trans {α : Type*} {step : α → Option α}
    {a b : α} {firstSteps secondSteps : ℕ} {P : α → Prop}
    (first : Computation.Trace step firstSteps a b)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ secondSteps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps + secondSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle htrace
  by_cases hprefix : prefixSteps ≤ firstSteps
  · exact hfirst prefixSteps intermediate hprefix htrace
  · exact hsecond (prefixSteps - firstSteps) intermediate (by omega)
      (trace_suffix htrace first (by omega))

theorem trace_prefix_bound_cons {α : Type*} {step : α → Option α}
    {a b : α} {steps : ℕ} {P : α → Prop}
    (hs : step a = some b) (ha : P a)
    (htail : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle hp
  cases hp with
  | refl => exact ha
  | cons hs' ht =>
      have heq := Option.some.inj (hs.symm.trans hs')
      subst b
      exact htail _ _ (by omega) ht


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
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

private theorem base_entry_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l) :
    StructuredProgram.entry c (label ∘ embed) (label exit) =
      label (StructuredProgram.entry c embed exit) := by
  induction c generalizing l L with
  | skip => rfl
  | atom => rfl
  | seq first second ihf ihs =>
      change StructuredProgram.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem base_code_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (site : StructuredProgram.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredProgram.code c embed exit site) =
      StructuredProgram.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | skip => exact site.elim
  | atom op => cases op <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredProgram.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [base_entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredProgram.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (base_entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (base_entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (base_entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem entry_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l) :
    StructuredCalls.entry c (label ∘ embed) (label exit) =
      label (StructuredCalls.entry c embed exit) := by
  induction c generalizing l L with
  | base c => exact base_entry_map c label embed exit
  | call => rfl
  | seq first second ihf ihs =>
      change StructuredCalls.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem code_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (site : StructuredCalls.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredCalls.code c embed exit site) =
      StructuredCalls.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | base c => exact base_code_map c label embed exit site
  | call p =>
      simp only [StructuredCalls.code]
      cases p.code site <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredCalls.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredCalls.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem commandLabel_sites {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    commandLabel c embed exit ∘ StructuredCalls.siteAddress c = embed := by
  funext site
  exact commandLabel_site c embed exit site

private theorem commandLabel_entry {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s) :
    commandLabel c embed exit (StructuredCalls.compiled c inputStack outputStack).entry =
      StructuredCalls.entry c embed exit := by
  change commandLabel c embed exit
    (StructuredCalls.entry c (StructuredCalls.siteAddress c) (StructuredCalls.exitAddress c)) = _
  rw [← entry_map c (commandLabel c embed exit) (StructuredCalls.siteAddress c)
    (StructuredCalls.exitAddress c), commandLabel_sites, commandLabel_exit]

private theorem commandLabel_code {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site)
    (pc : Fin (StructuredCalls.size c + 1)) (hpc : pc ≠ StructuredCalls.exitAddress c) :
    caller.code (commandLabel c embed exit pc) =
      ProgramLinking.relocateInstr id id (commandLabel c embed exit) none
        ((StructuredCalls.compiled c inputStack outputStack).code pc) := by
  obtain ⟨site, rfl⟩ : ∃ site, pc = StructuredCalls.siteAddress c site := by
    cases heq : (StructuredCalls.labelEquiv c).symm pc with
    | none =>
        have hp := congrArg (StructuredCalls.labelEquiv c) heq
        exact (hpc (by simpa [StructuredCalls.exitAddress] using hp)).elim
    | some site =>
        exact ⟨site, by simpa [StructuredCalls.siteAddress] using
          (congrArg (StructuredCalls.labelEquiv c) heq)⟩
  rw [commandLabel_site, StructuredCalls.compiled_site, code_map,
    commandLabel_sites, commandLabel_exit]
  exact hcode site

/-- A bound proved for one compiled structured block transfers to every
installation of that same block in a finite caller table. No bound on the
caller's total runtime is used. -/
theorem command_stack_bound {r s L : ℕ} {c : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval c steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled c inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled c inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry c embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  let routine := StructuredCalls.compiled c inputStack outputStack
  let label := commandLabel c embed exit
  let frame := a.withPC (some (StructuredCalls.entry c embed exit))
  have full := StructuredCalls.compiled_trace heval inputStack outputStack
  obtain ⟨source, hs⟩ := trace_prefix_exists full hle
  have hactive : source.pc ≠ none := by
    intro hnone
    have halted := ProgramLinking.trace_from_halted routine (trace_suffix full hs hle) hnone
    change some (StructuredCalls.exitAddress c) = none at halted
    cases halted
  have htable : ∀ pc, routine.code pc ≠ .halt →
      caller.code (label pc) = ProgramLinking.relocateInstr id id label none (routine.code pc) := by
    intro pc hnot
    apply commandLabel_code c caller embed exit inputStack outputStack hcode pc
    intro heq
    subst pc
    exact hnot (StructuredCalls.compiled_exit c inputStack outputStack)
  have hrelocated := ProgramLinking.relocate_trace_before_halt routine caller id id
    label none frame Function.injective_id Function.injective_id htable hs hactive
  have hinitial : ProgramLinking.embedCfg id id label none frame
      (a.withPC (some routine.entry)) = frame := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, routine, label, frame,
      StructuredProgram.State.withPC, commandLabel_entry]
  rw [hinitial] at hrelocated
  have heq := trace_same_length_unique hp hrelocated
  rw [heq]
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- A loop induction combines its current body and remaining iterations by
maximum space; the number of completed iterations never multiplies the bound. -/
theorem while_true_stack_bound {r s L : ℕ} {body : StructuredCalls.Cmd r s}
    {test : Fin r} {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (htest : a.regs test = true)
    (hb : StructuredCalls.Eval body n a b)
    (hw : StructuredCalls.Eval (.while test body) m b c)
    (inputStack outputStack : Fin s)
    (hbody : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hwhile : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := n + m)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry body (embed ∘ some) (embed none)))) ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hbody 0 _ (Nat.zero_le n) (.refl _)
  · exact trace_prefix_bound_trans
      (StructuredCalls.eval_trace hb caller (embed ∘ some) (embed none)
        (fun q => hcode (some q)))
      (command_stack_bound hb inputStack outputStack hbody caller (embed ∘ some)
        (embed none) (fun q => hcode (some q)))
      (command_stack_bound hw inputStack outputStack hwhile caller embed exit hcode)

theorem while_false_stack_bound {r s L : ℕ} (body : StructuredCalls.Cmd r s)
    (test : Fin r) {bound : ℕ} (a : StructuredCalls.State r s)
    (htest : a.regs test = false) (hstart : ∀ i, (a.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := 0)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some exit)) ?_ hstart ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · intro prefixSteps intermediate hle hp
    have hz : prefixSteps = 0 := by omega
    subst prefixSteps
    cases hp
    exact hstart

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: the mathematical depth-first transition and its count invariant.

The transition below specifies a leaf operation by its exact count. It is not a
primitive implementation of that operation, and no bit-time bound is asserted.
The pending list retains the current node and one sibling per branch on the
active path; completed leaves are discarded immediately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

open SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

theorem priority_literalMass_lt {M c : ℕ} {F : CNF (Fin n)} {H : Clause (Fin n)}
    (hM : 2 ≤ M) (hpriority : SparsePriority.Priority F M c H) :
    SunflowerBranch.literalMass (childA F c H) < SunflowerBranch.literalMass F ∧
      SunflowerBranch.literalMass (childB F c H) < SunflowerBranch.literalMass F := by
  obtain ⟨⟨C, hC, hc, hHC⟩, hpos, hproper, hdegree⟩ :=
    hpriority.spec
  have hsel : (selected F c H).Nonempty := ⟨C, mem_selected.mpr ⟨hC, hc, hHC⟩⟩
  have hpow : M ≤ M ^ (c - H.card) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < M)
      (by omega : 1 ≤ c - H.card)
  exact ⟨literalMass_childA_lt hsel hproper,
    literalMass_childB_lt (Finset.card_pos.mp hpos) hproper
      (hM.trans (hpow.trans hdegree))⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


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

theorem masked_sublist {α : Type*} (mask : List Bool) (C : List α) :
    (masked mask C).Sublist C := by
  induction C generalizing mask with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [masked]
    split
    · exact .cons_cons x (ih mask.tail)
    · exact .cons x (ih mask.tail)

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

theorem negatedUnits_set {V : Type*} [DecidableEq V] (H : List (Literal V)) :
    ExecCNF.formulaSet (negatedUnits Literal.negate H) =
      DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) := by
  ext C
  simp [negatedUnits, ExecCNF.formulaSet, ExecCNF.clauseSet,
    DisjointBranch.negatedCoreUnits, Finset.mem_image]

theorem resultA_set {V : Type*} [DecidableEq V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    ExecCNF.formulaSet (ExecCoreChildProgram.result F S H) =
      DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  simpa only [hS, DisjointBranch.childA, SAT.absorb] using
    ExecCoreChildProgram.result_set F S H

theorem units_disjoint_selected {V : Type*} [DecidableEq V]
    (F : CNF V) (c : ℕ) (H : Clause V) (hc : 2 ≤ c) :
    Disjoint (DisjointBranch.negatedCoreUnits H) (DisjointBranch.selected F c H) := by
  apply Finset.disjoint_left.mpr
  intro U hU hsel
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hU
  have hcard := (DisjointBranch.mem_selected.mp hsel).2.1
  rw [Finset.card_singleton] at hcard
  omega

theorem resultB_set {V : Type*} [DecidableEq V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ) (hc : 2 ≤ c)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    ExecCNF.formulaSet (resultB Literal.negate F S H) =
      DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  have hdisj := units_disjoint_selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) hc
  have hdiff :
      (DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) ∪ ExecCNF.formulaSet F) \
        DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) =
      DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) ∪
        (ExecCNF.formulaSet F \
          DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) := by
    rw [Finset.union_sdiff_distrib, hdisj.sdiff_eq_left]
  unfold resultB
  rw [ExecPetalChildProgram.result_set]
  change SAT.absorb (_ ∪ (_ \ _)) = _
  rw [ExecCNF.formulaSet_append, negatedUnits_set, hS, hdiff]
  unfold DisjointBranch.childB DisjointBranch.petals SunflowerBranch.petalFamily
  apply congrArg SAT.absorb
  ac_rfl

open BitProgram StructuredCalls

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CountDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed refinement of the concrete streaming frontier.

Depths and derivation trees below are proof indices. The physical pending tape
contains only formula bodies, and every formula keeps the same declared `Fin n`.
The selector and leaf execution contracts must still be supplied by their actual
finite programs; this module does not postulate a final counting service.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}

theorem childA_set (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n)))
    (hnodup : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (childA F c H) =
      DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) :=
  DisjointBranchProgram.resultA_set F (selectedRaw F c H) H c
    (selectedRaw_set F c H hnodup)

theorem childB_set (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n)))
    (hc : 2 ≤ c) (hnodup : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (childB F c H) =
      DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) :=
  DisjointBranchProgram.resultB_set F (selectedRaw F c H) H c hc
    (selectedRaw_set F c H hnodup)

open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCompletedTree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A completed concrete transition history determines a proof-only branch
forest backwards. This transfers the sharp tree-node bound to the actual
number of visits, without storing a tree or list of visits on the machine.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree

open SparseDFSRefinement
variable {n : ℕ}

theorem transition_potential_lt {k M : ℕ} {s t : Frontier n}
    (h : Transition k M s t) (hM : 2 ≤ M) : potential t < potential s := by
  cases h with
  | leaf node rest total hnone =>
    have hp : 0 < 3 ^ SunflowerBranch.literalMass (ExecCNF.formulaSet node.formula) :=
      Nat.pow_pos (by decide)
    simp only [potential, SparseCountProgram.potential, Frontier.model, Node.model,
      List.map_cons, List.sum_cons]
    omega
  | branch node rest total c H hv hp =>
    have priority := hp.toPriority (by omega) hv.width hv.literal_nodup hv.clause_nodup
    have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
    obtain ⟨ha, hb⟩ := SparseCountProgram.priority_literalMass_lt hM priority
    rw [← childA_set node.formula c H hv.literal_nodup] at ha
    rw [← childB_set node.formula c H hc hv.literal_nodup] at hb
    have powers : 3 ^ SunflowerBranch.literalMass (ExecCNF.formulaSet (childA node.formula c H)) +
        3 ^ SunflowerBranch.literalMass (ExecCNF.formulaSet (childB node.formula c H)) <
        3 ^ SunflowerBranch.literalMass (ExecCNF.formulaSet node.formula) := by
      generalize SunflowerBranch.literalMass (ExecCNF.formulaSet node.formula) = m at *
      cases m with
      | zero => omega
      | succ m =>
        have hpa := Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_of_lt_succ ha)
        have hpb := Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_of_lt_succ hb)
        have hpos : 0 < 3 ^ m := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega
    simp only [potential, SparseCountProgram.potential, Frontier.model, Node.model,
      List.map_cons, List.sum_cons]
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Well-founded assembly of the actual fixed DFS while command.
The body obligation is the concrete visit theorem; no finite successful run,
termination oracle, derivation tree or precomputed visit list is assumed.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

/-- This intermediate invariant is instantiated by the concrete prepared frame
and the proved per-visit resource envelope, before the final endpoint. -/
theorem execute_oai (k M : ℕ) (threshold : List Bool) (leaf : Code) (budget bound : ℕ)
    (I : Frontier n → Data → Prop) (hM : 2 ≤ M)
    (hboundary : ∀ s d, I s d → Boundary threshold s d)
    (hspace : ∀ s d, I s d → ∀ i, (d.stacks i).length ≤ bound)
    (hbody : ∀ (node : Node n) rest total d, I ⟨node :: rest, total⟩ d →
      ∃ next t, t ≤ budget ∧ ∃ e, BoundedEval (body k leaf) t d e bound ∧
        Transition k M ⟨node :: rest, total⟩ next ∧ I next e)
    (s : Frontier n) (d : Data) (hI : I s d) :
    ∃ visits t total e, t ≤ visits * (budget + 1) + 1 ∧
      BoundedEval (loop k leaf) t d e bound ∧
      Transitions k M visits s ⟨[], total⟩ ∧ I ⟨[], total⟩ e := by
  generalize hm : DFSCompletedTree.potential s = measure
  induction measure using Nat.strong_induction_on generalizing s d with
  | h measure ih =>
    rcases s with ⟨pending, total⟩
    cases pending with
    | nil =>
      have hf : d.regs 2 = false := by
        simpa using (hboundary ⟨[], total⟩ d hI).continue_flag
      refine ⟨0, 1, total, d, by simp, ⟨.while_false hf, ?_⟩, .refl _, hI⟩
      exact StructuredSpace.while_false_stack_bound (body k leaf) 2 d hf
        (hspace ⟨[], total⟩ d hI) (compiled (loop k leaf) 256 256)
        (siteAddress (loop k leaf)) (exitAddress (loop k leaf))
        (compiled_site (loop k leaf) 256 256)
    | cons node rest =>
      obtain ⟨next, tb, htb, afterBody, hb, transition, hnext⟩ :=
        hbody node rest total d hI
      have hlt : DFSCompletedTree.potential next < measure :=
        hm ▸ DFSCompletedTree.transition_potential_lt transition hM
      obtain ⟨visits, t, result, final, ht, he, transitions, hfinal⟩ :=
        ih _ hlt next afterBody hnext rfl
      have hf : d.regs 2 = true := by
        simpa using (hboundary ⟨node :: rest, total⟩ d hI).continue_flag
      refine ⟨visits + 1, tb + t + 1, result, final, ?_,
        ⟨.while_true hf hb.eval he.eval, ?_⟩, .cons transition transitions, hfinal⟩
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
      · exact StructuredSpace.while_true_stack_bound hf hb.eval he.eval 256 256
          hb.space he.space (compiled (loop k leaf) 256 256)
          (siteAddress (loop k leaf)) (exitAddress (loop k leaf))
          (compiled_site (loop k leaf) 256 256)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute_oai
