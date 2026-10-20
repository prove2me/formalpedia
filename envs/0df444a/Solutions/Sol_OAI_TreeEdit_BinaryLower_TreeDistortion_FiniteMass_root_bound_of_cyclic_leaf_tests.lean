-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.root_bound_of_cyclic_leaf_tests
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:11:12.625736+00:00
-- url     : https://prove2.me/submissions/fdebe524-20a7-40a2-9a8c-54faca4a8b06

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean:L394-L432
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.root_bound_of_cyclic_leaf_tests. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_character_root_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_subgroup_average_spectral_mass

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

/-- A character on the finite cyclic group is trivial exactly when its value
at the standard generator is one. -/
theorem zmod_character_eq_zero_iff (Q : ℕ) [NeZero Q]
    (χ : AddChar (ZMod Q) ℂ) : χ = 0 ↔ χ 1 = 1 := by
  constructor
  · intro h
    simp [h]
  · intro h
    apply AddChar.eq_zero_iff.mpr
    intro z
    have hz : z.val • (1 : ZMod Q) = z := by
      simp
    rw [← hz, χ.map_nsmul_eq_pow, h, one_pow]

/-- The coordinate version of the full-period leaf test, expressed using
the image of the cyclic generator. No injectivity of the subgroup map is needed. -/
theorem cyclic_average_spectral_mass {A : Type*}
    [AddCommGroup A] [Fintype A]
    (Q : ℕ) [NeZero Q] (φ : ZMod Q →+ A) (H : AddChar A ℂ → ℝ) :
    (∑ z : ZMod Q, ∑ χ : AddChar A ℂ, ‖1 - χ (φ z)‖ ^ 2 * H χ) /
        (Fintype.card (ZMod Q) : ℝ) =
      2 * ∑ χ : AddChar A ℂ, if χ (φ 1) = 1 then 0 else H χ := by
  classical
  rw [subgroup_average_spectral_mass]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  simp only [zmod_character_eq_zero_iff, AddChar.compAddMonoidHom_apply]

/-- A uniform upper bound on the displacement along a cyclic coordinate
bounds twice the spectral mass active on that coordinate. -/
theorem cyclic_active_mass_le {A : Type*} [AddCommGroup A] [Fintype A]
    (Q : ℕ) [NeZero Q] (φ : ZMod Q →+ A) (H : AddChar A ℂ → ℝ) (C : ℝ)
    (hcost : ∀ z : ZMod Q, (∑ χ, ‖1 - χ (φ z)‖ ^ 2 * H χ) ≤ C) :
    2 * (∑ χ : AddChar A ℂ, if χ (φ 1) = 1 then 0 else H χ) ≤ C := by
  classical
  rw [← cyclic_average_spectral_mass Q φ H]
  have hcard : (0 : ℝ) < Fintype.card (ZMod Q) :=
    Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hcard).2
  calc
    (∑ z : ZMod Q, ∑ χ, ‖1 - χ (φ z)‖ ^ 2 * H χ) ≤ ∑ _z : ZMod Q, C :=
      Finset.sum_le_sum (fun z _ => hcost z)
    _ = C * Fintype.card (ZMod Q) := by simp [nsmul_eq_mul, mul_comm]

/-- Cyclic leaf-coordinate translation bounds imply the character
root estimate. -/
theorem root_bound_of_cyclic_leaf_tests {A κ ν σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype κ] [Fintype ν] [Fintype σ]
    (Q : κ → ℕ) [∀ u, NeZero (Q u)] (φ : ∀ u, ZMod (Q u) →+ A)
    (H : AddChar A ℂ → ℝ) (root : A) (bad : ν → AddChar A ℂ → Prop)
    (a : ν → σ → AddChar A ℂ → ℝ) (B : ν → ℝ) (C : κ → ℝ)
    (M ε K : ℝ) (hK : 0 < K) (hH : ∀ χ, 0 ≤ H χ)
    (hdense : ∀ χ, χ root ≠ 1 → (¬ ∃ v, bad v χ) →
      K ≤ ((Finset.univ.filter (fun u => χ (φ u 1) ≠ 1)).card : ℝ))
    (hleaf : ∀ u (z : ZMod (Q u)),
      (∑ χ, ‖1 - χ (φ u z)‖ ^ 2 * H χ) ≤ C u)
    (hleafBudget : (∑ u, C u) ≤ M)
    (ha : ∀ v s χ, 0 ≤ a v s χ)
    (hdetect : ∀ v χ, bad v χ → 1 ≤ ∑ s, a v s χ)
    (hcost : ∀ v, (∑ s, ∑ χ, a v s χ * H χ) ≤ B v)
    (hbudget : (∑ v, B v) ≤ ε) :
    (∑ χ : AddChar A ℂ, ‖1 - χ root‖ ^ 2 * H χ) ≤
      4 * (ε + M / (2 * K)) := by
  classical
  apply character_root_bound H root (fun u χ => χ (φ u 1) ≠ 1)
    bad a B C M ε K hK hH
  · intro χ hr hb
    convert hdense χ hr hb using 1
    congr 1
    congr 1
    ext u
    simp
  · intro u
    convert cyclic_active_mass_le (Q u) (φ u) H (C u) (hleaf u) using 1
    congr 1
    congr 1
    funext χ
    by_cases hχ : χ (φ u 1) = 1 <;> simp [hχ]
  · exact hleafBudget
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


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.root_bound_of_cyclic_leaf_tests := @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.root_bound_of_cyclic_leaf_tests
