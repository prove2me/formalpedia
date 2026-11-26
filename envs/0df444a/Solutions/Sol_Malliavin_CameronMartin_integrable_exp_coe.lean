-- Prove2me | solution 1 for Malliavin.CameronMartin.integrable_exp_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:14.158859+00:00
-- url     : https://prove2.me/submissions/28680ddf-df1a-48ef-9fc2-885060f67891

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
import Theorems.Thm_Malliavin_CameronMartin_map_coe_eq_gaussianReal
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
    Integrable (fun x ↦ Real.exp ((h : Lp ℝ 2 μ) x)) μ := by
  have hi : Integrable (fun y : ℝ ↦ Real.exp (1 * y))
      (gaussianReal 0 (‖h‖₊ ^ 2)) := integrable_exp_mul_gaussianReal 1
  have himap : Integrable (fun y : ℝ ↦ Real.exp (1 * y))
      (μ.map ((h : Lp ℝ 2 μ) : W → ℝ)) := by
    rw [map_coe_eq_gaussianReal μ h]
    exact hi
  change Integrable ((fun y : ℝ ↦ Real.exp y) ∘
    ((h : Lp ℝ 2 μ) : W → ℝ)) μ
  simpa only [one_mul] using
    himap.comp_aemeasurable (Lp.aestronglyMeasurable (h : Lp ℝ 2 μ)).aemeasurable
end Malliavin.CameronMartin
