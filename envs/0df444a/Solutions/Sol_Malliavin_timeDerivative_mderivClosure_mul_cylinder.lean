-- Prove2me | solution 1 for Malliavin.timeDerivative_mderivClosure_mul_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:25.516988+00:00
-- url     : https://prove2.me/submissions/00d0b048-5b32-4ab5-9554-9ee40c74409f

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_coeFn_boundedSMul
import Theorems.Thm_Malliavin_coeFn_smulLp
import Theorems.Thm_Malliavin_mderiv_cylindrical
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_timeDerivative_boundedSMul
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
  {φ : ℝ → ℝ} {K : ℝ≥0}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P
        ((memLp_mul_smoothBounded P (isSmoothBounded_cylinder L hL f hf ⟨C, hb⟩ hb' t) F).toLp
          _)) =
      boundedSMul (G := fun p : ℝ≥0 × W ↦ f (fun i ↦ B (t i) p.2))
          (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
            (isSmoothBounded_cylinder L hL f hf ⟨C, hb⟩ hb' t).continuous.aestronglyMeasurable)
          (fun _ ↦ hb _) (timeDerivative hB L hL hgen (mderivClosure P F)) +
        ∑ i, tensor (intervalIndicator (t i))
          ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _) := by
  set G := fun w ↦ f (fun i ↦ B (t i) w) with hGdef
  have hG : IsSmoothBounded G := isSmoothBounded_cylinder L hL f hf ⟨C, hb⟩ hb' t
  rw [(mul_mem_domD12 P hG hF).2]
  -- split the derivative
  have hsplit : (memLp_mul_deriv P hG F (mderivClosure P F)).toLp _ =
      boundedSMul (G := G) hG.continuous.aestronglyMeasurable (fun x ↦ hb _)
          (mderivClosure P F) +
        ∑ i, smulLp (ofDual P (L (t i)))
          ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _) := by
    apply Lp.ext
    have h4 := ae_all_iff.2 fun i ↦ coeFn_smulLp (ofDual P (L (t i)))
      ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _)
    have h5 := ae_all_iff.2 fun i ↦
      MemLp.coeFn_toLp (memLp_mul_cylinderPartial L hL f hf hb' t F i)
    filter_upwards [MemLp.coeFn_toLp (memLp_mul_deriv P hG F (mderivClosure P F)),
      Lp.coeFn_add (boundedSMul (G := G) hG.continuous.aestronglyMeasurable (fun x ↦ hb _)
        (mderivClosure P F)) (∑ i, smulLp (ofDual P (L (t i)))
          ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _)),
      coeFn_boundedSMul (G := G) hG.continuous.aestronglyMeasurable (fun x ↦ hb _)
        (mderivClosure P F),
      Lp.coeFn_finsetSum Finset.univ (fun i ↦ smulLp (ofDual P (L (t i)))
        ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _)), h4, h5]
      with w h1 h2 h3 h6 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h6, Finset.sum_apply]
    simp_rw [h4, h5]
    congr 1
    have hF' : G = fun w ↦ f (fun i ↦ L (t i) w) := by
      funext w
      simp only [hGdef, hL]
    have hBL : (fun j ↦ B (t j) w) = fun j ↦ L (t j) w := by
      funext j
      simp only [hL]
    rw [hF', mderiv_cylindrical P f (fun i ↦ L (t i)) w ((hf.differentiable one_ne_zero) _),
      hBL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_smul]
  rw [hsplit, map_add, timeDerivative_boundedSMul hB L hL hgen]
  congr 1
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ smulLp (ofDual P (L (t i)))
      ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _)) Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [timeDerivative_smulLp hB L hL hgen, wienerIntegralEquiv_symm_ofDual hB L hL hgen]
end Malliavin
