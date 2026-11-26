-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_polynomial_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:06:55.951828+00:00
-- url     : https://prove2.me/submissions/662aee6b-c436-47fd-bc64-b752ed90a4d0

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a
import Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp_brownian
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
variable {g : ℝ → ℝ}
namespace Malliavin
theorem _root_.solution (hgen : IsWienerGenerated B)
    (p : Polynomial ℝ) (T : ℝ≥0) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_polynomial_brownian L hL p T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_polynomial_derivative_brownian L hL p T).toLp _) := by
  have h := timeDerivative_mderivClosure_comp_brownian hB L hL hgen (contDiff_polynomial_eval p)
    (add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)) (Nat.cast_nonneg _)
    (abs_polynomial_eval_le' p) (abs_polynomial_deriv_le' p) T
    (by simpa only [Polynomial.deriv] using memLp_polynomial_derivative_brownian L hL p T)
  simpa only [Polynomial.deriv] using h
end Malliavin
