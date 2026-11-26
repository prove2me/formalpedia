-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivLp_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:05.937547+00:00
-- url     : https://prove2.me/submissions/5d653428-5be9-4a15-975e-67ba21b92300

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_timeDerivative_smulLp
import Theorems.Thm_Malliavin_wienerIntegralEquiv_symm_ofDual
import Theorems.Thm_Malliavin_mderivLp_cylinder
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
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
variable (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
namespace Malliavin
theorem _root_.solution (hgen : IsWienerGenerated B) {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hb : ∃ C, ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) :
    timeDerivative hB L hL hgen ((isSmoothBounded_cylinder L hL f hf hb hb' t).mderivLp P) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartial L hL f hf hb' t i) := by
  rw [mderivLp_cylinder L hL f hf hb hb' t]
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i)) Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [timeDerivative_smulLp hB L hL hgen, wienerIntegralEquiv_symm_ofDual hB L hL hgen]
end Malliavin
