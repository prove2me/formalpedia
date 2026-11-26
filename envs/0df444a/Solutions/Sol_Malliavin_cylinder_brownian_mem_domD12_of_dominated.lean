-- Prove2me | solution 1 for Malliavin.cylinder_brownian_mem_domD12_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:07.970575+00:00
-- url     : https://prove2.me/submissions/8708809b-4a96-4afc-8b70-eec1a5c5ac79

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_cylinder_mem_domD12_of_dominated
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_coeFn_smulLp
import Theorems.Thm_Malliavin_mderiv_cylindrical
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
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf : ∀ y, |f y| ≤ φ y)
    (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ : ∀ m x, φ (truncCoord m (fun i ↦ L (t i)) x) ≤ ψ x)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P) :
    (memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i) := by
  have hF : (memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _ =
      (memLp_cylinder_of_dominated P hf (fun i ↦ L (t i)) hφf hψ' hint).toLp _ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint),
      MemLp.coeFn_toLp (memLp_cylinder_of_dominated P hf (fun i ↦ L (t i)) hφf hψ' hint)]
      with w h1 h2
    rw [h1, h2]
    simp only [hL]
  obtain ⟨hmem, hder⟩ :=
    cylinder_mem_domD12_of_dominated P hf (fun i ↦ L (t i)) hφf hφf' hψ hψ' hint
  rw [hF]
  refine ⟨hmem, hder.trans ?_⟩
  apply Lp.ext
  have hpart : ∀ᵐ w ∂P, ∀ i : Fin n,
      (smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i) : W → Space P) w =
        fderiv ℝ f (fun j ↦ L (t j) w) (Pi.single i 1) • ofDual P (L (t i)) :=
    ae_all_iff.2 fun i ↦ by
      filter_upwards [coeFn_smulLp (ofDual P (L (t i)))
          (cylinderPartialD L hL hf hφf' t hψ' hint i),
        MemLp.coeFn_toLp (memLp_cylinderPartial_of_dominated L hL hf hφf' t hψ' hint i)]
        with w h1 h2
      rw [h1, cylinderPartialD, h2]
      simp only [hL]
  filter_upwards [MemLp.coeFn_toLp
      (memLp_mderiv_cylinder_of_dominated P hf (fun i ↦ L (t i)) hφf' hψ' hint),
    Lp.coeFn_finsetSum Finset.univ
      (fun i ↦ smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i)), hpart]
    with w h1 h2 h3
  rw [h1, h2, Finset.sum_apply]
  simp_rw [h3]
  exact mderiv_cylindrical P f (fun i ↦ L (t i)) w (hf.differentiable one_ne_zero _)
end Malliavin
