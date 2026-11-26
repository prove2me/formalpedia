-- Prove2me | solution 1 for Malliavin.CameronMartin.density_mul_neg_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:55:59.597421+00:00
-- url     : https://prove2.me/submissions/0278600b-2471-42b7-9e2c-c47275c037d5

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_realDensity_pos
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_realDensity_mul_neg_ae
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
    (fun x ↦ density μ h x * density μ (-h) x) =ᵐ[μ]
      fun _ ↦ ENNReal.ofReal (Real.exp (-‖h‖ ^ 2)) := by
  filter_upwards [realDensity_mul_neg_ae μ h] with x hx
  simp only [density]
  rw [← ENNReal.ofReal_mul (realDensity_pos μ h x).le, hx]
end Malliavin.CameronMartin
