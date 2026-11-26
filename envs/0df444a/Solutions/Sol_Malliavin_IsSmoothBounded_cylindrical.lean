-- Prove2me | solution 1 for Malliavin.IsSmoothBounded.cylindrical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:36.399865+00:00
-- url     : https://prove2.me/submissions/4d3490e5-0377-41b8-9952-129c24e10f5c

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
open Malliavin.IsSmoothBounded
variable {μ} {F G : W → ℝ}
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin.IsSmoothBounded
theorem _root_.solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C) (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (L : Fin n → StrongDual ℝ W) :
    IsSmoothBounded (fun x ↦ f (fun i ↦ L i x)) := by
  set Λ : W →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.pi L with hΛ
  have hcomp : (fun x ↦ f (fun i ↦ L i x)) = f ∘ Λ := by
    funext x
    simp only [hΛ, ContinuousLinearMap.coe_pi', Function.comp_apply]
  rw [hcomp]
  refine ⟨hf.comp Λ.contDiff, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun x ↦ hC _⟩
  · obtain ⟨C, hC⟩ := hb'
    refine ⟨C * ‖Λ‖, fun x ↦ ?_⟩
    rw [fderiv_comp x (hf.differentiable one_ne_zero _) Λ.differentiableAt, Λ.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (ContinuousLinearMap.opNorm_nonneg _))
end Malliavin.IsSmoothBounded
