-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.finite_spectral_root_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:13:14.768641+00:00
-- url     : https://prove2.me/submissions/2b0786f1-198f-4baf-a588-8e527f915531

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean:L452-L487
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.finite_spectral_root_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_root_bound_of_cyclic_leaf_tests

-- ---- from OAI.Combinatorics.BinaryEdit.SparseActivity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Sparse activity in a finite branching construction

Sparse/dense Fourier-mass estimates for `prop:finite-lower`.
-/

namespace TreeEdit.BinaryLower.TreeDistortion.FiniteMass

open scoped BigOperators
open Classical

/-- Normalizing finitely many tests preserves a uniform test budget. -/
theorem normalized_weighted_test_bound {ι σ : Type*}
    [Fintype ι] [Fintype σ] [Nonempty σ]
    (H : ι → ℝ) (a : σ → ι → ℝ) (B : ℝ)
    (hcost : ∀ s, (∑ i, a s i * H i) ≤ B) :
    (∑ s, ∑ i, (a s i / (Fintype.card σ : ℝ)) * H i) ≤ B := by
  have hcard : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  have heq : (∑ s, ∑ i, (a s i / (Fintype.card σ : ℝ)) * H i) =
      (∑ s, ∑ i, a s i * H i) / (Fintype.card σ : ℝ) := by
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [heq]
  apply (div_le_iff₀ hcard).2
  calc
    (∑ s, ∑ i, a s i * H i) ≤ ∑ _s : σ, B :=
      Finset.sum_le_sum (fun s _ => hcost s)
    _ = B * Fintype.card σ := by simp [nsmul_eq_mul, mul_comm]

/-- Complete finite spectral aggregation with concrete leaf and internal
translations. Geometry supplies the stated translation budgets; short-period
averaging supplies `hdetect`; branching supplies `hdense`. No additional
Fourier-mass or exceptional-union assertion is assumed. -/
theorem finite_spectral_root_bound {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν]
    [Fintype σ] [Nonempty σ]
    (Q : κ → ℕ) [∀ u, NeZero (Q u)] (φ : ∀ u, ZMod (Q u) →+ A)
    (H : AddChar A ℂ → ℝ) (root : A) (bad : ν → AddChar A ℂ → Prop)
    (shift : ν → σ → A) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => χ (φ u 1) ≠ 1)).card : ℝ))
    (hleaf : ∀ u (z : ZMod (Q u)),
      (∑ χ, ‖1 - χ (φ u z)‖ ^ 2 * H χ) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (hdetect : ∀ v χ, bad v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s, (∑ χ, ‖1 - χ (shift v s)‖ ^ 2 * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.mpr Fintype.card_pos
  apply root_bound_of_cyclic_leaf_tests Q φ H root bad
    (fun v s χ => ‖1 - χ (shift v s)‖ ^ 2 / (Fintype.card σ : ℝ))
    B C M ε K hK hH hdense hleaf hleafBudget
  · intro v s χ
    exact div_nonneg (sq_nonneg _) (le_of_lt hcard)
  · intro v χ hb
    rw [← Finset.sum_div]
    exact (le_div_iff₀ hcard).2 (by simpa using hdetect v χ hb)
  · intro v
    exact normalized_weighted_test_bound H (fun s χ => ‖1 - χ (shift v s)‖ ^ 2)
      (B v) (hcost v)
  · exact hbudget

end TreeEdit.BinaryLower.TreeDistortion.FiniteMass

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TreeDistortion OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.finite_spectral_root_bound := @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.finite_spectral_root_bound
