-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.integral_mul_polynomial_centeredGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:08.391306+00:00
-- url     : https://prove2.me/submissions/fe070afb-2e8b-4434-b2c8-4dc37d4749b1

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_pow_succ_centeredGaussian
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integrable_polynomial_centeredGaussian
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
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
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (variance : ℝ≥0) (p : Polynomial ℝ) :
    (∫ x : ℝ, x * p.eval x ∂gaussianReal 0 variance) =
      (variance : ℝ) * ∫ x : ℝ, p.derivative.eval x ∂gaussianReal 0 variance := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hxp : Integrable (fun x : ℝ ↦ x * p.eval x)
          (gaussianReal 0 variance) := by
        refine (integrable_polynomial_centeredGaussian variance
          (Polynomial.X * p)).congr <| Filter.Eventually.of_forall fun x ↦ ?_
        simp only [Polynomial.eval_mul, Polynomial.eval_X]
      have hxq : Integrable (fun x : ℝ ↦ x * q.eval x)
          (gaussianReal 0 variance) := by
        refine (integrable_polynomial_centeredGaussian variance
          (Polynomial.X * q)).congr <| Filter.Eventually.of_forall fun x ↦ ?_
        simp only [Polynomial.eval_mul, Polynomial.eval_X]
      simp only [Polynomial.eval_add, mul_add, Polynomial.derivative_add]
      rw [integral_add hxp hxq,
        integral_add (integrable_polynomial_centeredGaussian variance p.derivative)
          (integrable_polynomial_centeredGaussian variance q.derivative), hp, hq]
      ring
  | monomial n a =>
      simp only [Polynomial.eval_monomial, Polynomial.derivative_monomial]
      calc
        (∫ x : ℝ, x * (a * x ^ n) ∂gaussianReal 0 variance) =
            a * ∫ x : ℝ, x ^ (n + 1) ∂gaussianReal 0 variance := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          rw [pow_succ]
          ring
        _ = a * ((variance : ℝ) * n *
            ∫ x : ℝ, x ^ (n - 1) ∂gaussianReal 0 variance) := by
          rw [integral_pow_succ_centeredGaussian]
        _ = (variance : ℝ) *
            ∫ x : ℝ, a * n * x ^ (n - 1) ∂gaussianReal 0 variance := by
          rw [integral_const_mul]
          ring
end Malliavin.BrownianIteratedConstruction
