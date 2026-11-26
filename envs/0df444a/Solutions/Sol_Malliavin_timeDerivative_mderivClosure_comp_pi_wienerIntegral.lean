-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_comp_pi_wienerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:37.497379+00:00
-- url     : https://prove2.me/submissions/0408dfec-0b83-483a-be8b-2dacacd848b0

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_mderivClosure_comp_pi_space
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_timeDerivative_smulLp
import Theorems.Thm_Malliavin_wienerIntegral_mem_space
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
  {φ : ℝ → ℝ} {K : ℝ≥0}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen (mderivClosure P
        ((memLp_comp_pi P hf hK fun i ↦ wienerIntegral hB (g i)).toLp _)) =
      ∑ i, tensor (g i)
        ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral hB (g i)) i).toLp _) := by
  have hmem : ∀ i, wienerIntegral hB (g i) ∈ Space P := fun i ↦
    wienerIntegral_mem_space hB L hL hgen (g i)
  rw [mderivClosure_comp_pi_space hf hK fun i ↦ ⟨_, hmem i⟩]
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ smulLp (⟨_, hmem i⟩ : Space P)
      ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral hB (g i)) i).toLp _)) Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [timeDerivative_smulLp hB L hL hgen]
  congr 1
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl
end Malliavin
