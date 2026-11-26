-- Prove2me | solution 1 for Malliavin.CameronMartin.integral_exp_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:21.209815+00:00
-- url     : https://prove2.me/submissions/03eee30f-c8a8-4fac-88be-e17f5d922d0a

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
import Theorems.Thm_Malliavin_CameronMartin_variance_coe_eq_norm_sq
import Theorems.Thm_Malliavin_CameronMartin_space_hasGaussianLaw
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
    ∫ x, Real.exp ((h : Lp ℝ 2 μ) x) ∂μ = Real.exp (‖h‖ ^ 2 / 2) := by
  have hmgf := mgf_gaussianReal (space_hasGaussianLaw μ h).map_eq_gaussianReal 1
  rw [integral_coe_eq_zero μ h, Real.coe_toNNReal _
    (variance_nonneg (fun x ↦ (h : Lp ℝ 2 μ) x) μ),
    variance_coe_eq_norm_sq μ h] at hmgf
  simpa [mgf] using hmgf
end Malliavin.CameronMartin
