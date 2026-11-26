-- Prove2me | solution 1 for Malliavin.mderiv_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:19.935803+00:00
-- url     : https://prove2.me/submissions/fda2181f-d1fe-4ef8-bda0-b91632fdf0dd

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
namespace Malliavin
theorem _root_.solution {F : W → ℝ} {x : W} {φ : ℝ → ℝ} (hφ : DifferentiableAt ℝ φ (F x))
    (hF : DifferentiableAt ℝ F x) :
    mderiv μ (fun y ↦ φ (F y)) x = deriv φ (F x) • mderiv μ F x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_mderiv, Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_left,
    ← Submodule.coe_inner, inner_mderiv]
  have hcomp : (fun y ↦ φ (F y)) = φ ∘ F := rfl
  rw [hcomp, fderiv_comp x hφ hF, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv]
  simp only [inclusion_apply, smul_eq_mul, mul_comm]
end Malliavin
