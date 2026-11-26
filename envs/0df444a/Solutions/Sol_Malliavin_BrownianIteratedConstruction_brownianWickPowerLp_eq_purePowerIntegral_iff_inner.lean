-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_eq_purePowerIntegral_iff_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:02.707307+00:00
-- url     : https://prove2.me/submissions/4c43c38d-abe7-4a06-9f11-97bd740d3a4d

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_norm_sq_brownianPurePowerIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_norm_sq_brownianWickPowerLp
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
attribute [local simp] Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n =
        brownianPurePowerIntegral hB n (stepToLp v) ↔
      inner ℝ (brownianWickPowerLp hB v n)
          (brownianPurePowerIntegral hB n (stepToLp v)) =
        (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by
  constructor
  · intro heq
    rw [heq, real_inner_self_eq_norm_sq,
      norm_sq_brownianPurePowerIntegral hB hsm n (stepToLp v)]
  · intro hinner
    let X := brownianWickPowerLp hB v n
    let Y := brownianPurePowerIntegral hB n (stepToLp v)
    change X = Y
    change inner ℝ X Y =
      (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n at hinner
    have hX : ‖X‖ ^ 2 =
        (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by
      exact norm_sq_brownianWickPowerLp hB v n
    have hY : ‖Y‖ ^ 2 =
        (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by
      exact norm_sq_brownianPurePowerIntegral hB hsm n (stepToLp v)
    have hdiffInner : inner ℝ (X - Y) (X - Y) = 0 := by
      rw [real_inner_sub_sub_self, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq, hX, hinner, hY]
      ring
    have hdiffNorm : ‖X - Y‖ ^ 2 = 0 := by
      simpa only [real_inner_self_eq_norm_sq] using hdiffInner
    have hnormZero : ‖X - Y‖ = 0 := by
      nlinarith [norm_nonneg (X - Y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormZero)
end Malliavin.BrownianIteratedConstruction
