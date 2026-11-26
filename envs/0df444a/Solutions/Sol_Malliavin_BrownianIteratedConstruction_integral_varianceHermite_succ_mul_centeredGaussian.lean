-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.integral_varianceHermite_succ_mul_centeredGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:54.988149+00:00
-- url     : https://prove2.me/submissions/dc08a8cf-7791-4baf-bcc1-ce921435343f

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
theorem _root_.solution
    (variance : ℝ≥0) (m n : ℕ) :
    (∫ x : ℝ, (varianceHermite (variance : ℝ) (m + 1)).eval x *
        (varianceHermite (variance : ℝ) n).eval x ∂gaussianReal 0 variance) =
      (variance : ℝ) * n *
        ∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) (n - 1)).eval x
          ∂gaussianReal 0 variance := by
  rw [varianceHermite_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, sub_mul]
  have hfirst : Integrable (fun x : ℝ ↦
      x * (varianceHermite (variance : ℝ) m).eval x *
        (varianceHermite (variance : ℝ) n).eval x)
      (gaussianReal 0 variance) := by
    refine (integrable_polynomial_centeredGaussian variance
      (Polynomial.X * varianceHermite (variance : ℝ) m *
        varianceHermite (variance : ℝ) n)).congr <|
          Filter.Eventually.of_forall fun x ↦ ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
  have hsecond : Integrable (fun x : ℝ ↦
      ((variance : ℝ) * m *
        (varianceHermite (variance : ℝ) (m - 1)).eval x) *
          (varianceHermite (variance : ℝ) n).eval x)
      (gaussianReal 0 variance) := by
    refine (integrable_polynomial_centeredGaussian variance
      (Polynomial.C ((variance : ℝ) * m) *
        varianceHermite (variance : ℝ) (m - 1) *
          varianceHermite (variance : ℝ) n)).congr <|
            Filter.Eventually.of_forall fun x ↦ ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [integral_sub hfirst hsecond]
  have hstein := integral_mul_polynomial_centeredGaussian variance
    (varianceHermite (variance : ℝ) m * varianceHermite (variance : ℝ) n)
  simp only [Polynomial.eval_mul] at hstein
  have hstein' :
      (∫ x : ℝ, x * (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) =
        (variance : ℝ) *
          ∫ x : ℝ, ((varianceHermite (variance : ℝ) m *
            varianceHermite (variance : ℝ) n).derivative).eval x
            ∂gaussianReal 0 variance := by
    calc
      (∫ x : ℝ, x * (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) =
          ∫ x : ℝ, x * ((varianceHermite (variance : ℝ) m).eval x *
            (varianceHermite (variance : ℝ) n).eval x)
            ∂gaussianReal 0 variance := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := hstein
  rw [hstein']
  have hderiv :
      (∫ x : ℝ, ((varianceHermite (variance : ℝ) m *
          varianceHermite (variance : ℝ) n).derivative).eval x
          ∂gaussianReal 0 variance) =
        m * (∫ x : ℝ, (varianceHermite (variance : ℝ) (m - 1)).eval x *
          (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) +
        n * (∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) (n - 1)).eval x
          ∂gaussianReal 0 variance) := by
    rw [Polynomial.derivative_mul, derivative_varianceHermite,
      derivative_varianceHermite]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    have hleft : Integrable (fun x : ℝ ↦
        (m * (varianceHermite (variance : ℝ) (m - 1)).eval x) *
          (varianceHermite (variance : ℝ) n).eval x)
        (gaussianReal 0 variance) := by
      refine (integrable_polynomial_centeredGaussian variance
        (Polynomial.C (m : ℝ) * varianceHermite (variance : ℝ) (m - 1) *
          varianceHermite (variance : ℝ) n)).congr <|
            Filter.Eventually.of_forall fun x ↦ ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
    have hright : Integrable (fun x : ℝ ↦
        (varianceHermite (variance : ℝ) m).eval x *
          (n * (varianceHermite (variance : ℝ) (n - 1)).eval x))
        (gaussianReal 0 variance) := by
      refine (integrable_polynomial_centeredGaussian variance
        (varianceHermite (variance : ℝ) m * Polynomial.C (n : ℝ) *
          varianceHermite (variance : ℝ) (n - 1))).congr <|
            Filter.Eventually.of_forall fun x ↦ ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring
    rw [integral_add hleft hright]
    have hleftIntegral :
        (∫ x : ℝ, (m * (varianceHermite (variance : ℝ) (m - 1)).eval x) *
            (varianceHermite (variance : ℝ) n).eval x
            ∂gaussianReal 0 variance) =
          m * ∫ x : ℝ, (varianceHermite (variance : ℝ) (m - 1)).eval x *
            (varianceHermite (variance : ℝ) n).eval x
            ∂gaussianReal 0 variance := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    have hrightIntegral :
        (∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
            (n * (varianceHermite (variance : ℝ) (n - 1)).eval x)
            ∂gaussianReal 0 variance) =
          n * ∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
            (varianceHermite (variance : ℝ) (n - 1)).eval x
            ∂gaussianReal 0 variance := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hleftIntegral, hrightIntegral]
  rw [hderiv]
  have hsecondIntegral :
      (∫ x : ℝ, ((variance : ℝ) * m *
          (varianceHermite (variance : ℝ) (m - 1)).eval x) *
            (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) =
        (variance : ℝ) * m *
          ∫ x : ℝ, (varianceHermite (variance : ℝ) (m - 1)).eval x *
            (varianceHermite (variance : ℝ) n).eval x
            ∂gaussianReal 0 variance := by
    calc
      (∫ x : ℝ, ((variance : ℝ) * m *
          (varianceHermite (variance : ℝ) (m - 1)).eval x) *
            (varianceHermite (variance : ℝ) n).eval x
          ∂gaussianReal 0 variance) =
          ∫ x : ℝ, ((variance : ℝ) * m) *
            ((varianceHermite (variance : ℝ) (m - 1)).eval x *
              (varianceHermite (variance : ℝ) n).eval x)
            ∂gaussianReal 0 variance := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := by rw [integral_const_mul]
  rw [hsecondIntegral]
  ring
end Malliavin.BrownianIteratedConstruction
