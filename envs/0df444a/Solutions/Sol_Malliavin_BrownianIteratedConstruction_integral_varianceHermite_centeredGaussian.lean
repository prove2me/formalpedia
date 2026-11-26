-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.integral_varianceHermite_centeredGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:20:12.669265+00:00
-- url     : https://prove2.me/submissions/6a7e963b-46b6-40e7-b7cd-8a0ecbdf6e7b

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integrable_polynomial_centeredGaussian
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_mul_polynomial_centeredGaussian
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_derivative_varianceHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_varianceHermite_succ
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
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (variance : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, (varianceHermite (variance : ℝ) n).eval x
      ∂gaussianReal 0 variance) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [varianceHermite]
  | succ n =>
      simp only [Nat.succ_ne_zero, if_false]
      rw [varianceHermite_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C]
      have hx : Integrable (fun x : ℝ ↦ x *
          (varianceHermite (variance : ℝ) n).eval x)
          (gaussianReal 0 variance) := by
        refine (integrable_polynomial_centeredGaussian variance
          (Polynomial.X * varianceHermite (variance : ℝ) n)).congr <|
            Filter.Eventually.of_forall fun x ↦ ?_
        simp only [Polynomial.eval_mul, Polynomial.eval_X]
      have hc : Integrable (fun x : ℝ ↦
          ((variance : ℝ) * n) *
            (varianceHermite (variance : ℝ) (n - 1)).eval x)
          (gaussianReal 0 variance) :=
        (integrable_polynomial_centeredGaussian variance
          (varianceHermite (variance : ℝ) (n - 1))).const_mul _
      rw [integral_sub hx hc, integral_mul_polynomial_centeredGaussian,
        derivative_varianceHermite]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      rw [integral_const_mul, integral_const_mul]
      ring
end Malliavin.BrownianIteratedConstruction
