-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_wickExp_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:15.218487+00:00
-- url     : https://prove2.me/submissions/d5b215e9-9ae8-4099-bc6d-87d9f9cf9443

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_deriv_exp_sub
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
theorem _root_.solution (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_wickExp_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_wickExp_brownian L hL T).toLp _) := by
  have h := timeDerivative_mderivClosure_comp_brownian hB L hL hgen (contDiff_exp_sub (T / 2))
    zero_le_one zero_le_one (fun x ↦ abs_exp_sub_le_exp_abs (T / 2) x (by positivity))
    (fun x ↦ by rw [deriv_exp_sub]; exact abs_exp_sub_le_exp_abs (T / 2) x (by positivity)) T
    (by simpa only [deriv_exp_sub] using memLp_wickExp_brownian L hL T)
  simpa only [deriv_exp_sub] using h
end Malliavin
