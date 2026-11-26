-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.integral_pow_succ_centeredGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:39.833848+00:00
-- url     : https://prove2.me/submissions/5e6c0456-49c5-41fb-87e0-78cead1ae79a

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
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
theorem _root_.solution (variance : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 1) ∂gaussianReal 0 variance) =
      (variance : ℝ) * n * ∫ x : ℝ, x ^ (n - 1) ∂gaussianReal 0 variance := by
  have hmoment (k : ℕ) :
      (∫ x : ℝ, x ^ k ∂gaussianReal 0 variance) =
        iteratedDeriv k (mgf (fun x : ℝ ↦ x) (gaussianReal 0 variance)) 0 := by
    rw [iteratedDeriv_mgf_zero (by simp)]
    rfl
  rw [hmoment (n + 1), hmoment (n - 1), mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  have hderiv :
      deriv (fun t : ℝ ↦ Real.exp ((variance : ℝ) * t ^ 2 / 2)) =
        fun t ↦ (variance : ℝ) * t * Real.exp ((variance : ℝ) * t ^ 2 / 2) := by
    funext t
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
      Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul,
      deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
    ring
  rw [iteratedDeriv_succ', hderiv]
  simp only [mul_assoc]
  rw [iteratedDeriv_const_mul_field]
  apply congrArg (fun z : ℝ ↦ (variance : ℝ) * z)
  have hmul := iteratedDeriv_mul (n := n) (x := (0 : ℝ))
    (f := id) (g := fun t : ℝ ↦ Real.exp ((variance : ℝ) * t ^ 2 / 2))
    (by fun_prop) (by fun_prop)
  change iteratedDeriv n
    (id * fun t : ℝ ↦ Real.exp ((variance : ℝ) * t ^ 2 / 2)) 0 = _
  rw [hmul]
  cases n with
  | zero => simp [iteratedDeriv_id]
  | succ n =>
      rw [Finset.sum_eq_single 1]
      · simp [iteratedDeriv_id]
      · intro b _hb hb1
        simp [iteratedDeriv_id, hb1]
      · simp
end Malliavin.BrownianIteratedConstruction
