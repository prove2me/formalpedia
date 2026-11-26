-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_comp_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:00.005785+00:00
-- url     : https://prove2.me/submissions/f0c20a0c-8ccd-4080-b76c-2f0cb8fe0d1f

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_mderivClosure_comp_pi_eq_sum_boundedSMul
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_timeDerivative_boundedSMul
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
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 P} (hF : ∀ i, F i ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_comp_pi P hf hK F).toLp _)) =
      ∑ i, boundedSMul (G := fun p : ℝ≥0 × W ↦ fderiv ℝ f (fun i ↦ F i p.2) (Pi.single i 1))
          (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
            (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable) (C := K)
        (fun _ ↦ abs_fderiv_pi_single_le hK _ i)
        (timeDerivative hB L hL hgen (mderivClosure P (F i))) := by
  rw [mderivClosure_comp_pi_eq_sum_boundedSMul hf hK hF]
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ boundedSMul (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
      (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
      (fun x ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i))) Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun i _ ↦ timeDerivative_boundedSMul hB L hL hgen _ _ _
end Malliavin
