-- Prove2me | solution 1 for Malliavin.CameronMartin.expectationMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:54.146525+00:00
-- url     : https://prove2.me/submissions/4eeed614-f348-433e-9265-c7af5076d4fa

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
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply


attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero

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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin.CameronMartin
theorem _root_.solution (f : Lp ℝ 2 μ) :
    expectationMap μ f = ∫ x, f x ∂μ := by
  rw [expectationMap, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  simp only [Lp.const_val, AEEqFun.coeFn_const_eq, ContinuousLinearMap.mul_apply', mul_one]
end Malliavin.CameronMartin
