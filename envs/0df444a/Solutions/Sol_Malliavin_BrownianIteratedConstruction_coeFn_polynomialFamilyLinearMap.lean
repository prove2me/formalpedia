-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.coeFn_polynomialFamilyLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:16:20.581463+00:00
-- url     : https://prove2.me/submissions/91d98cab-a761-4145-944f-bf8e5015b624

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
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


attribute [local simp] Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
variable {M : Type*} [AddCommMonoid M] [Module ℝ M]
variable {W : Type*} [MeasurableSpace W] {P : Measure W}
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (xpow : ℕ → Lp ℝ 2 P) (X : W → ℝ)
    (hxpow : ∀ n, (xpow n : W → ℝ) =ᵐ[P] fun w ↦ X w ^ n)
    (p : Polynomial ℝ) :
    (polynomialFamilyLinearMap xpow p : W → ℝ) =ᵐ[P]
      fun w ↦ p.eval (X w) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      filter_upwards [Lp.coeFn_add (polynomialFamilyLinearMap xpow p)
        (polynomialFamilyLinearMap xpow q), hp, hq] with w hadd hpw hqw
      rw [hadd, Pi.add_apply, hpw, hqw, Polynomial.eval_add]
  | monomial n a =>
      have hmonomial : Polynomial.monomial n a =
          a • (Polynomial.X : Polynomial ℝ) ^ n := by
        rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hmonomial, map_smul, polynomialFamilyLinearMap_X_pow]
      filter_upwards [Lp.coeFn_smul a (xpow n), hxpow n] with w hsmul hpow
      rw [hsmul, Pi.smul_apply, hpow, Polynomial.eval_smul]
      simp only [smul_eq_mul, Polynomial.eval_pow, Polynomial.eval_X]
end Malliavin.BrownianIteratedConstruction
