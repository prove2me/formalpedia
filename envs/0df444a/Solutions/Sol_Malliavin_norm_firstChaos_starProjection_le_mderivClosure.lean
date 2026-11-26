-- Prove2me | solution 1 for Malliavin.norm_firstChaos_starProjection_le_mderivClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:20.151807+00:00
-- url     : https://prove2.me/submissions/6267b320-8e6a-4cbf-ba49-4ad0be53d829

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_inner_mderivClosure_const
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution
    {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    ‖(firstChaos μ).starProjection F‖ ≤ ‖mderivClosure μ F‖ := by
  let q : Space μ := (firstChaos μ).orthogonalProjectionOnto F
  change ‖q‖ ≤ ‖mderivClosure μ F‖
  have hproj : ⟪F, (q : Lp ℝ 2 μ)⟫_ℝ = ‖q‖ ^ 2 := by
    rw [real_inner_comm]
    calc
      ⟪(q : Lp ℝ 2 μ), F⟫_ℝ =
          ⟪q, (firstChaos μ).orthogonalProjectionOnto F⟫_ℝ := by
        rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
      _ = ⟪q, q⟫_ℝ := by rfl
      _ = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q
  have hconst :
      ‖(memLp_const (μ := μ) (p := 2) q).toLp (fun _ : W ↦ q)‖ = ‖q‖ := by
    change ‖Lp.const 2 μ q‖ = ‖q‖
    rw [Lp.norm_const (p := 2) (μ := μ) (c := q) (by norm_num)]
    simp only [probReal_univ, Real.one_rpow, mul_one]
  have hsq : ‖q‖ ^ 2 ≤ ‖mderivClosure μ F‖ * ‖q‖ := by
    calc
      ‖q‖ ^ 2 = ⟪mderivClosure μ F,
          (memLp_const (μ := μ) (p := 2) q).toLp (fun _ : W ↦ q)⟫_ℝ := by
        rw [inner_mderivClosure_const μ hF q, hproj]
      _ ≤ ‖mderivClosure μ F‖ *
          ‖(memLp_const (μ := μ) (p := 2) q).toLp (fun _ : W ↦ q)‖ :=
        real_inner_le_norm (F := Lp (Space μ) 2 μ) _ _
      _ = ‖mderivClosure μ F‖ * ‖q‖ := by rw [hconst]
  by_cases hq : q = 0
  · rw [hq, norm_zero]
    exact norm_nonneg (mderivClosure μ F)
  · rw [pow_two] at hsq
    exact le_of_mul_le_mul_right hsq (norm_pos_iff.mpr hq)
end Malliavin
