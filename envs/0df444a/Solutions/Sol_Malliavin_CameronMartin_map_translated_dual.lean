-- Prove2me | solution 1 for Malliavin.CameronMartin.map_translated_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:21.736994+00:00
-- url     : https://prove2.me/submissions/e777c229-4552-4e69-9b02-b71754b156aa

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
import Theorems.Thm_Malliavin_CameronMartin_centeredDualToLp_ae_eq
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
theorem _root_.solution (h : Space μ) (L : StrongDual ℝ W) :
    (translated μ h).map L =
      gaussianReal (L (mean μ) + L (inclusion μ h)) (‖ofDual μ L‖₊ ^ 2) := by
  have hcoe : Measurable ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  calc (translated μ h).map L
      = μ.map (L ∘ translate (inclusion μ h)) := by
        unfold translated translatedMeasure
        rw [Measure.map_map L.continuous.measurable (measurable_translate _)]
    _ = μ.map ((fun y ↦ y + (L (mean μ) + L (inclusion μ h))) ∘
          ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ)) := by
        apply Measure.map_congr
        filter_upwards [centeredDualToLp_ae_eq μ L] with x hx
        simp only [Function.comp_apply, translate, map_add, coe_ofDual, hx]
        ring
    _ = (μ.map ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ)).map
          (fun y ↦ y + (L (mean μ) + L (inclusion μ h))) := by
        rw [Measure.map_map (by fun_prop) hcoe]
    _ = gaussianReal (L (mean μ) + L (inclusion μ h)) (‖ofDual μ L‖₊ ^ 2) := by
        rw [map_coe_eq_gaussianReal μ (ofDual μ L), gaussianReal_map_add_const, zero_add]
end Malliavin.CameronMartin
