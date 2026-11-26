-- Prove2me | solution 1 for Malliavin.CameronMartin.integral_add_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:28.493554+00:00
-- url     : https://prove2.me/submissions/9462dbf2-39be-4204-8e34-d584af189c11

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_measurable_density
import Theorems.Thm_Malliavin_CameronMartin_density_ne_top
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_translated_eq_withDensity
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply


attribute [local simp] Malliavin.CameronMartin.density_toReal

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
theorem _root_.solution {F : W → ℝ} (hF : Continuous F) (h : Space μ) :
    ∫ x, F (x + inclusion μ h) ∂μ =
      ∫ x, F x * Real.exp ((h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2) ∂μ := by
  have h1 : ∫ x, F (x + inclusion μ h) ∂μ = ∫ x, F x ∂(translated μ h) := by
    unfold translated translatedMeasure
    rw [integral_map (measurable_translate _).aemeasurable hF.aestronglyMeasurable]
    rfl
  rw [h1, translated_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (measurable_density μ h) (Filter.Eventually.of_forall fun x ↦ (density_ne_top μ h x).lt_top)]
  congr 1
  funext x
  rw [density_toReal, smul_eq_mul, mul_comm]
  rfl
end Malliavin.CameronMartin
