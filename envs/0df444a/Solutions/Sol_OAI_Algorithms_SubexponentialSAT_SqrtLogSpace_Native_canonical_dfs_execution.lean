-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:36:15.342267+00:00
-- url     : https://prove2.me/submissions/4c77f1e6-8b78-4e39-8b80-c8ac70bc64d5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCompletedTree_completed_visits_reciprocal
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCountProgram_command_execution

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete finite CNF syntax and semantics for the candidate SAT argument. -/

namespace SubexponentialSAT.SAT

universe u

variable {V : Type u}

variable [DecidableEq V]

section Decidable

theorem normalize_not_tautology {F : CNF V} {C : Clause V} (hC : C ∈ normalize F) :
    ¬ C.IsTautology :=
  (Finset.mem_filter.mp (absorb_subset (removeTautologies F) hC)).2

end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SunflowerBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem antichain_normalize (F : CNF V) : Antichain (normalize F) :=
  antichain_absorb _

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

theorem dedupLiterals_nodup (C : Clause α) : (dedupLiterals C).Nodup := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih
    · simp only [dedupLiterals, ite_eq_right h, List.nodup_cons]
      exact ⟨fun hm => h ((contains_true x xs).mpr ((mem_dedupLiterals x xs).mp hm)), ih⟩

theorem dedupLiterals_length_le (C : Clause α) : (dedupLiterals C).length ≤ C.length := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih.trans (Nat.le_succ _)
    · simpa [dedupLiterals, h] using Nat.succ_le_succ ih

theorem dedupClauses_map_nodup (F : Formula α) : ((dedupClauses F).map clauseSet).Nodup := by
  induction F with
  | nil => simp [dedupClauses]
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simpa [dedupClauses, h] using ih
    · simp only [dedupClauses, ite_eq_right h, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hm
      have hmem : clauseSet C ∈ formulaSet (dedupClauses F) := by
        exact List.mem_toFinset.mpr hm
      rw [formulaSet_dedupClauses] at hmem
      exact h ((any_equivalent_true C F).mpr hmem)

end SubexponentialSAT.ExecCNF

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

theorem dedupClauses_subset (F : Formula α) : dedupClauses F ⊆ F := by
  intro C hC
  induction F with
  | nil => simp [dedupClauses] at hC
  | cons D F ih =>
    by_cases h : F.any (fun E => equivalent D E) = true
    · have htail : C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact List.mem_cons_of_mem D (ih htail)
    · have hsplit : C = D ∨ C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact hsplit.elim (fun h => h ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem D (ih h))

theorem absorb_subset (F : Formula α) : absorb F ⊆ F := by
  intro C hC
  exact dedupClauses_subset F (List.mem_filter.mp hC).1

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

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem absorb_map_nodup (F : Formula α) : ((absorb F).map clauseSet).Nodup := by
  apply List.Sublist.nodup _ (dedupClauses_map_nodup F)
  exact List.Sublist.map clauseSet List.filter_sublist

theorem normalize_map_nodup (neg : α → α) (F : Formula α) :
    ((normalize neg F).map clauseSet).Nodup := absorb_map_nodup _

theorem normalize_literal_nodup (neg : α → α) (F : Formula α) :
    ∀ C ∈ normalize neg F, C.Nodup := by
  intro C hC
  have h1 := absorb_subset _ hC
  have h2 := (List.mem_filter.mp h1).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h2
  exact dedupLiterals_nodup D

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

@[simp] theorem dedupLiterals_length (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

@[simp] theorem dedupClauses_length (F : Formula α) :
    (dedupClauses F).length = (formulaSet F).card := by
  have h := List.toFinset_card_of_nodup (dedupClauses_map_nodup F)
  change (formulaSet (dedupClauses F)).card = _ at h
  rw [formulaSet_dedupClauses, List.length_map] at h
  exact h.symm

end SubexponentialSAT.ExecSunflowerSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecQuantitativeSparsify
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Quantitative bounds for the executable list sparsifier

This module instantiates the actual list search and depth-first worklist at the
arithmetically selected inverse budget. The finite-set view of each output is
used only for SAT semantics. Node visits are counted by the actual worklist;
they are not presented as primitive bit-machine transitions.
-/

namespace SubexponentialSAT.ExecQuantitativeSparsify

open SAT

variable {n : ℕ}

theorem formulaList_width (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    ExecSunflowerSearch.RawWidthAtMost k (formulaList F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  simpa only [literalList_length] using hF D ((mem_orderedClauses F D).mp hD)

end SubexponentialSAT.ExecQuantitativeSparsify

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFCodeTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

theorem dedupLiterals_eq_of_nodup (C : Clause α) (hC : C.Nodup) : dedupLiterals C = C := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hC
      have h : ¬ contains x xs = true := by simpa only [contains_true] using hx
      simp only [dedupLiterals, ite_eq_right h, ih hxs]

theorem cleanLiterals_eq_of_nodup (F : Formula α) (hF : ∀ C ∈ F, C.Nodup) :
    cleanLiterals F = F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [cleanLiterals, List.map_cons]
      rw [dedupLiterals_eq_of_nodup C (hF C (by simp))]
      congr 1
      exact ih (fun D hD => hF D (by simp [hD]))

@[simp] theorem cleanLiterals_normalize (neg : α → α) (F : Formula α) :
    cleanLiterals (normalize neg F) = normalize neg F :=
  cleanLiterals_eq_of_nodup _ (normalize_literal_nodup neg F)

/-- The extra pass in the typed worklist does not alter order or multiplicity. -/
theorem normalizedInput_eq_normalize {n : ℕ}
    (F : Formula (SAT.Literal (Fin n))) :
    ExecSparsifyWorklist.normalizedInput F = normalize SAT.Literal.negate F := by
  exact cleanLiterals_normalize SAT.Literal.negate F

end SubexponentialSAT.ExecCNFCodeTransport

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

theorem normalize_width_le (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) :
    ∀ C ∈ ExecCNF.normalize SAT.Literal.negate F, C.length ≤ k := by
  intro C hC
  have h₁ := ExecCNF.absorb_subset _ hC
  have h₂ := (List.mem_filter.mp h₁).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h₂
  exact (ExecCNF.dedupLiterals_length_le D).trans (h D hD)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open SparseCharging

theorem chooseExponent_spec (k a b : ℕ) (ha : 0 < a) :
    parameterTest k a b (chooseExponent k a b ha) = true :=
  Nat.find_spec (exists_parameter k a b ha)

theorem chooseM_spec (k a b : ℕ) (ha : 0 < a) :
    2 ≤ chooseM k a b ha ∧ rightConstant k ≤ chooseM k a b ha ∧
      rightConstant k * Nat.clog 2 (4 * depthConstant k (chooseM k a b ha) *
        chooseM k a b ha) * b ≤ a * chooseM k a b ha := by
  simpa only [parameterTest, chooseM, decide_eq_true_eq] using chooseExponent_spec k a b ha


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CanonicalFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual canonical normalizer emits the ordered body consumed by the
disjoint DFS. Both sides retain the declared ambient variable universe. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem canonical_normalized_formula {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpNormalizationCorrectness.normalizedFormula F =
      ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F) :=
  ExecCNFCodeTransport.normalizedInput_eq_normalize _

theorem canonical_normalized_body {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpNormalizationCorrectness.normalizedBody F =
      DisjointReuse.SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate
        (ExecQuantitativeSparsify.formulaList F)) := by
  unfold SubexpNormalizationCorrectness.normalizedBody
  rw [canonical_normalized_formula]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
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


theorem Valid.normalize (F : RawCNF n) {k : ℕ} (hw : ∀ C ∈ F, C.length ≤ k) :
    Valid k (ExecCNF.normalize Literal.negate F) := by
  refine ⟨ExecCNF.normalize_literal_nodup _ _, ExecCNF.normalize_map_nodup _ _,
    normalize_width_le F hw, ?_, ?_⟩
  · rw [ExecCNF.normalize_set]
    exact SunflowerBranch.antichain_normalize _
  · rw [ExecCNF.normalize_set]
    exact fun _ hC => SAT.normalize_not_tautology hC

open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativePrepared
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual canonical setup frame supplies the exact disjoint DFS ports.
No declared coordinate is compressed, and the threshold is the computed
reciprocal-budget choice used by the sharp visit bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem SetupReady.dfs_prepared {k n : ℕ} {F : SAT.CNF (Fin n)}
    {a : State 80 1220} (h : SetupReady k F a) :
    DFSStartup.Prepared (a.stacks 259)
      (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) a := by
  refine ⟨h.blank 257 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.header, rfl,
    h.blank 260 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 261 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 262 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 263 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.body.trans (canonical_normalized_body F), ?_⟩
  intro i hi
  apply h.blank i
  · intro he
    subst i
    change 256 < 256 at hi
    omega
  all_goals intro he; subst i; omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeDFSIntegration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Connect the actual produced setup frame to canonical exact counting.
The remaining finite leaf-command and numerical-envelope premises are explicit
development seams, to be instantiated by the streamed native leaf integration. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem canonical_dfs_execution_oai {n : ℕ} (k : ℕ) (hk : 2 ≤ k)
    (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost k F)
    (a : State 80 1220) (ready : SetupReady k F a) (hs : 0 < sparsifySchedule n)
    (leaf : Cmd 80 1220) (leafTime inputBound bound : ℕ)
    (hinput : ∀ i, (a.stacks i).length ≤ inputBound)
    (hstartup : 1220 * inputBound +
      8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 17 ≤ bound)
    (hvisit : DFSCountProgram.visitSpace k n F.card
      (a.stacks 259).length ≤ bound)
    (hleaf : DFSVisit.LeafContract (n := n) k (a.stacks 259) inputBound
      leaf leafTime bound) :
    ∃ visits t b,
      t ≤ 8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 16 +
        (visits * (DFSVisit.visitTime k n (SparseCountProgram.formulaBound n k)
          (a.stacks 259).length leafTime bound + 1) + 1) + (2 * bound + 7 * n + 18) ∧
      DFSVisit.BoundedEval (DFSCountProgram.command k leaf) t a b
        (1224 * bound + 7 * n + 19) ∧
      b.stacks 256 = countWord (SAT.count F) ∧
      (visits : ℝ) ≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n) := by
  have hwidth := ExecQuantitativeSparsify.formulaList_width F k hw
  have hM : 2 ≤ toNat (a.stacks 259) := by
    rw [ready.threshold]
    exact (SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by decide)).1
  obtain ⟨visits, t, b, ht, he, hout, history⟩ :=
    DFSCountProgram.command_execution k (a.stacks 259) leaf
      (ExecQuantitativeSparsify.formulaList F) a leafTime inputBound bound hk hM hwidth
      ready.dfs_prepared ready.occurrence ready.dimension ready.dimension_length hinput
      (by simpa only [← canonical_normalized_body] using hstartup)
      (by simpa only [ExecQuantitativeSparsify.formulaList_length] using hvisit) hleaf
  have htree := DFSCompletedTree.completed_visits_reciprocal k (sparsifySchedule n)
    hk hs (SparseDFSRefinement.Valid.normalize _ hwidth)
    (by simpa only [ready.threshold] using history)
  refine ⟨visits, t, b, ?_, he, ?_, htree⟩
  · simpa only [← canonical_normalized_body] using ht
  · simpa only [rawCount, ExecQuantitativeSparsify.formulaList_set] using hout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution_oai
