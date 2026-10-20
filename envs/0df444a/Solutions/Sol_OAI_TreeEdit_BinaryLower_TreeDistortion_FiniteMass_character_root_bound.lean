-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_root_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:04:45.219978+00:00
-- url     : https://prove2.me/submissions/44965440-794b-4b33-a382-11b66565af26

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean:L265-L301
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_root_bound. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_weighted_active_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_weighted_detection_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_weighted_union_bound

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

/-- Combining detectors at all nodes gives the exceptional-character mass
estimate used before the sparse/dense dichotomy. -/
theorem exceptional_mass_of_detectors {ι ν σ : Type*}
    [Fintype ι] [Fintype ν] [Fintype σ]
    (H : ι → ℝ) (a : ν → σ → ι → ℝ) (bad : ν → ι → Prop)
    (B : ν → ℝ) (hH : ∀ i, 0 ≤ H i)
    (ha : ∀ v s i, 0 ≤ a v s i)
    (hdetect : ∀ v i, bad v i → 1 ≤ ∑ s, a v s i)
    (hcost : ∀ v, (∑ s, ∑ i, a v s i * H i) ≤ B v) :
    (∑ i, if ∃ v, bad v i then H i else 0) ≤ ∑ v, B v := by
  classical
  apply (weighted_union_bound H bad hH).trans
  apply Finset.sum_le_sum
  intro v _
  exact (weighted_detection_bound H (a v) (bad v) hH (ha v) (hdetect v)).trans (hcost v)

/-- The finite obstruction's root estimate in terms of nonnegative Fourier
weights and geometric detector bounds. -/
theorem root_bound_of_detectors {ι ν σ : Type*}
    [Fintype ι] [Fintype ν] [Fintype σ]
    (H w μ : ι → ℝ) (active : ι → Prop) (bad : ν → ι → Prop)
    (a : ν → σ → ι → ℝ) (B : ν → ℝ) (M ε K : ℝ)
    (hK : 0 < K) (hH : ∀ i, 0 ≤ H i) (hw : ∀ i, 0 ≤ w i)
    (hμ : ∀ i, μ i ≤ 4) (hzero : ∀ i, ¬ active i → μ i = 0)
    (hdense : ∀ i, active i → (¬ ∃ v, bad v i) → K ≤ w i)
    (hleaf : 2 * ∑ i, w i * H i ≤ M)
    (ha : ∀ v s i, 0 ≤ a v s i)
    (hdetect : ∀ v i, bad v i → 1 ≤ ∑ s, a v s i)
    (hcost : ∀ v, (∑ s, ∑ i, a v s i * H i) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ i, μ i * H i) ≤ 4 * (ε + M / (2 * K)) := by
  classical
  apply weighted_active_bound H w μ active (fun i => ∃ v, bad v i)
    M ε K hK hH hw hμ hzero hdense hleaf
  convert! (exceptional_mass_of_detectors H a bad B hH ha hdetect hcost).trans hbudget using 1
  congr 1
  funext i
  by_cases hi : ∃ v, bad v i <;> simp [hi]

/-- Counting active coordinates commutes with summing nonnegative Fourier
weights. The identity itself does not require weight nonnegativity. -/
theorem support_mass_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : ι → ℝ) (activeLeaf : κ → ι → Prop) :
    (∑ i, ((Finset.univ.filter (fun u => activeLeaf u i)).card : ℝ) * H i) =
      ∑ u, ∑ i, if activeLeaf u i then H i else 0 := by
  classical
  have hpoint : ∀ i,
      ((Finset.univ.filter (fun u => activeLeaf u i)).card : ℝ) * H i =
        ∑ u, if activeLeaf u i then H i else 0 := by
    intro i
    rw [← Finset.sum_filter]
    simp
  simp_rw [hpoint]
  exact Finset.sum_comm

/-- The per-leaf cyclic-average cost estimates imply the weighted leaf-mass
bound. This is equation (finite-leaf-mass) before insertion of the tree costs. -/
theorem leaf_mass_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : ι → ℝ) (activeLeaf : κ → ι → Prop) (C : κ → ℝ) (M : ℝ)
    (hleaf : ∀ u, 2 * (∑ i, if activeLeaf u i then H i else 0) ≤ C u)
    (hbudget : (∑ u, C u) ≤ M) :
    2 * (∑ i, ((Finset.univ.filter (fun u => activeLeaf u i)).card : ℝ) * H i) ≤ M := by
  classical
  rw [support_mass_identity, Finset.mul_sum]
  exact (Finset.sum_le_sum (fun u _ => hleaf u)).trans hbudget

/-- Every spectral multiplier of a finite-group character is at most four. -/
theorem character_multiplier_le_four {A : Type*} [AddCommGroup A] [Fintype A]
    (χ : AddChar A ℂ) (z : A) : ‖1 - χ z‖ ^ 2 ≤ 4 := by
  have hnorm := norm_sub_le (1 : ℂ) (χ z)
  rw [norm_one, χ.norm_apply] at hnorm
  nlinarith [norm_nonneg (1 - χ z)]

/-- Character-specialized root estimate. The root activity and multiplier
are the actual complex character values, rather than unrelated predicates.
This is the spectral aggregation step in the finite-tree obstruction. -/
theorem character_root_bound {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν] [Fintype σ]
    (H : AddChar A ℂ → ℝ) (root : A)
    (activeLeaf : κ → AddChar A ℂ → Prop) (bad : ν → AddChar A ℂ → Prop)
    (a : ν → σ → AddChar A ℂ → ℝ) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => activeLeaf u χ)).card : ℝ))
    (hleaf : ∀ u, 2 * (∑ χ, if activeLeaf u χ then H χ else 0) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (ha : ∀ v s χ, 0 ≤ a v s χ)
    (hdetect : ∀ v χ, bad v χ → 1 ≤ ∑ s, a v s χ)
    (hcost : ∀ v, (∑ s, ∑ χ, a v s χ * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by
  classical
  apply root_bound_of_detectors H
    (fun χ => ((Finset.univ.filter (fun u => activeLeaf u χ)).card : ℝ))
    (fun χ => ‖1 - χ root‖ ^ 2) (fun χ => χ root ≠ 1)
    bad a B M ε K hK hH
  · intro χ
    exact Nat.cast_nonneg _
  · intro χ
    exact character_multiplier_le_four χ root
  · intro χ hχ
    have heq : χ root = 1 := not_not.mp hχ
    simp [heq]
  · exact hdense
  · exact leaf_mass_bound H activeLeaf C M hleaf hleafBudget
  · exact ha
  · exact hdetect
  · exact hcost
  · exact hbudget

end TreeEdit.BinaryLower.TreeDistortion.FiniteMass

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TreeDistortion OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_root_bound := @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_root_bound
