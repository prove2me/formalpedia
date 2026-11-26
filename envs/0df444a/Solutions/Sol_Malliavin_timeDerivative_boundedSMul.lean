-- Prove2me | solution 1 for Malliavin.timeDerivative_boundedSMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:55.352612+00:00
-- url     : https://prove2.me/submissions/17a0efd4-ec5c-495e-add3-07fe93fc8dde

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_P2M_Malliavin_compLp___boundedSMul_3f896ab5bcad
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_fubiniLift_boundedSMul
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
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) {G : W → ℝ}
    (hG : AEStronglyMeasurable G P) {C : ℝ} (hC : ∀ x, |G x| ≤ C) (U : Lp (Space P) 2 P) :
    timeDerivative hB L hL hgen (boundedSMul hG hC U) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure) hG)
        (fun p ↦ hC p.2) (timeDerivative hB L hL hgen U) := by
  unfold timeDerivative timeDerivativeOfEq timeDerivativeOfFirstChaos
  simp only [LinearIsometry.coe_comp, Function.comp_apply]
  rw [compLpₗᵢ_boundedSMul, compLpₗᵢ_boundedSMul, fubiniLift_boundedSMul]
end Malliavin
