-- Prove2me | solution 1 for Malliavin.CameronMartin.variance_coe_eq_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:34.831447+00:00
-- url     : https://prove2.me/submissions/6d57c757-4441-494e-a9e4-32e55c360ff7

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_integral_coe_eq_zero
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply


attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology
noncomputable section
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8
open Malliavin Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin.CameronMartin
theorem _root_.solution (h : Space μ) :
    Var[fun x ↦ (h : Lp ℝ 2 μ) x; μ] = ‖h‖ ^ 2 := by
  rw [variance_of_integral_eq_zero
    (Lp.aestronglyMeasurable (h : Lp ℝ 2 μ)).aemeasurable
    (integral_coe_eq_zero μ h)]
  calc
    ∫ x, (h : Lp ℝ 2 μ) x ^ 2 ∂μ =
        @inner ℝ _ _ (h : Lp ℝ 2 μ) (h : Lp ℝ 2 μ) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [pow_two, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq,
        abs_mul_abs_self]
    _ = ‖(h : Lp ℝ 2 μ)‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = ‖h‖ ^ 2 := by rfl
end Malliavin.CameronMartin
