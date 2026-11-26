-- Prove2me | solution 1 for Malliavin.mderivLp_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:51.175803+00:00
-- url     : https://prove2.me/submissions/101db7a1-e2d4-4459-afd0-c5778fd0a1a1

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
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
theorem _root_.solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C) (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) :
    (isSmoothBounded_cylinder L hL f hf hb hb' t).mderivLp P =
      ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i) := by
  apply Lp.ext
  have hpart : ∀ᵐ w ∂P, ∀ i : Fin n,
      (smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i) : W → Space P) w =
        fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1) • ofDual P (L (t i)) :=
    ae_all_iff.2 fun i ↦ by
      filter_upwards [coeFn_smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i),
        MemLp.coeFn_toLp (memLp_cylinderPartial L hL f hf hb' t i)] with w h1 h2
      rw [h1, cylinderPartial, h2]
  filter_upwards [MemLp.coeFn_toLp ((isSmoothBounded_cylinder L hL f hf hb hb' t).memLp_mderiv P 2),
    Lp.coeFn_finsetSum Finset.univ
      (fun i ↦ smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i)), hpart]
    with w h1 h2 h3
  rw [IsSmoothBounded.mderivLp, h1, h2, Finset.sum_apply]
  simp_rw [h3]
  have hF : (fun w ↦ f (fun i ↦ B (t i) w)) = fun w ↦ f (fun i ↦ L (t i) w) := by
    funext w
    simp only [hL]
  have hBL : (fun j ↦ B (t j) w) = fun j ↦ L (t j) w := by
    funext j
    simp only [hL]
  rw [hF, mderiv_cylindrical P f (fun i ↦ L (t i)) w ((hf.differentiable one_ne_zero) _), hBL]
end Malliavin
