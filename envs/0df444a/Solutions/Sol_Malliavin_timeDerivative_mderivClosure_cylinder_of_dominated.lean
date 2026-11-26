-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_cylinder_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:05.661581+00:00
-- url     : https://prove2.me/submissions/b0e92b98-17ca-46ea-aa11-92f94e3fd45d

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_cylinder_brownian_mem_domD12_of_dominated
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
import Theorems.Thm_Malliavin_wienerIntegralEquiv_symm_ofDual
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
namespace Malliavin
theorem _root_.solution (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf : ∀ y, |f y| ≤ φ y) (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ : ∀ m x, φ (truncCoord m (fun i ↦ L (t i)) x) ≤ ψ x)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _)) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartialD L hL hf hφf' t hψ' hint i) := by
  rw [(cylinder_brownian_mem_domD12_of_dominated L hL hf hφf hφf' t hψ hψ' hint).2]
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i))
    Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [timeDerivative_smulLp hB L hL hgen, wienerIntegralEquiv_symm_ofDual hB L hL hgen]
end Malliavin
