-- Prove2me | solution 1 for Malliavin.CameronMartin.densityExponent_neg_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:38.998832+00:00
-- url     : https://prove2.me/submissions/6f1cca30-558f-4076-a974-2163a6c39add

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply


attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.density_zero

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
omit [CompleteSpace W] [SecondCountableTopology W]
namespace Malliavin.CameronMartin
theorem _root_.solution (h : Space μ) :
    densityExponent μ (-h) =ᵐ[μ]
      fun x ↦ -(h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2 := by
  filter_upwards [Lp.coeFn_neg (h : Lp ℝ 2 μ)] with x hx
  change (((-h : Space μ) : Lp ℝ 2 μ) : W → ℝ) x =
    -((h : Lp ℝ 2 μ) : W → ℝ) x at hx
  simp only [densityExponent, norm_neg]
  rw [hx]
end Malliavin.CameronMartin
