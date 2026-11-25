-- Prove2me | solution 1 for GlobalTheory.NodalCubic.nonsingular_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:40.727591+00:00
-- url     : https://prove2.me/submissions/534fb3ac-038e-46ea-9af3-5f608b5078a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
import Theorems.Thm_GlobalTheory_NodalCubic_addXYZ_param
import Theorems.Thm_GlobalTheory_NodalCubic_dblXYZ_param
import Theorems.Thm_GlobalTheory_NodalCubic_eq_of_param_equiv
import Theorems.Thm_GlobalTheory_NodalCubic_nonsingular_iff_nodal
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NodalCubic
namespace GlobalTheory.NodalCubic
theorem _root_.solution : ∀ (k : Type) [Field k], (∀ u : kˣ, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular ![(u : k) * (1 - u), (u : k) ^ 2, (1 - (u : k)) ^ 3]) ∧ (∀ u v : kˣ, ∃ c : kˣ, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.add ![(u : k) * (1 - u), (u : k) ^ 2, (1 - (u : k)) ^ 3] ![(v : k) * (1 - v), (v : k) ^ 2, (1 - (v : k)) ^ 3] = (c : k) • ![((u * v : kˣ) : k) * (1 - (u * v : kˣ)), ((u * v : kˣ) : k) ^ 2, (1 - ((u * v : kˣ) : k)) ^ 3]) ∧ ∀ P : Fin 3 → k, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular P → P 1 ≠ 0 ∧ P 0 + P 1 ≠ 0 ∧ ∃ c : kˣ, P = (c : k) • ![(P 1 / (P 0 + P 1)) * (1 - P 1 / (P 0 + P 1)), (P 1 / (P 0 + P 1)) ^ 2, (1 - P 1 / (P 0 + P 1)) ^ 3] := by
  intro k _
  refine ⟨fun u => ?_, fun u v => ?_, fun P hP => ?_⟩
  · rw [nonsingular_iff_nodal]
    refine ⟨by simp; ring, Or.inr (Or.inr ?_)⟩
    have : ((u : k) ^ 2) ^ 2 + (u : k) * (1 - u) * (u : k) ^ 2 = (u : k) ^ 3 := by ring
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, this]
    exact pow_ne_zero 3 u.ne_zero
  · by_cases h : (u : k) = v
    · refine ⟨u ^ 3, ?_⟩
      rw [Units.val_mul, ← h, WeierstrassCurve.Projective.add_self, dblXYZ_param, Units.val_pow_eq_pow_val]
    · refine ⟨Units.mk0 (((u : k) - v) ^ 3) (pow_ne_zero 3 (sub_ne_zero.mpr h)), ?_⟩
      rw [WeierstrassCurve.Projective.add_of_not_equiv
        (fun h' => h (eq_of_param_equiv u.ne_zero v.ne_zero h')), addXYZ_param, Units.val_mul, Units.val_mk0]
  · rw [nonsingular_iff_nodal] at hP
    obtain ⟨he, hn⟩ := hP
    have key : P 1 * (P 0 + P 1) ≠ 0 := by
      intro h0
      have hx : P 0 = 0 := by
        have : P 0 ^ 3 = 0 := by linear_combination P 2 * h0 - he
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hy : P 1 = 0 := by
        rw [hx, zero_add] at h0
        exact mul_self_eq_zero.mp h0
      simp [hx, hy] at hn
    have hy : P 1 ≠ 0 := left_ne_zero_of_mul key
    have hs : P 0 + P 1 ≠ 0 := right_ne_zero_of_mul key
    refine ⟨hy, hs, Units.mk0 ((P 0 + P 1) ^ 2 / P 1) (div_ne_zero (pow_ne_zero 2 hs) hy), ?_⟩
    ext i
    fin_cases i
    · simp
      field_simp
      ring
    · simp
      field_simp
    · simp
      field_simp
      linear_combination he
end GlobalTheory.NodalCubic
