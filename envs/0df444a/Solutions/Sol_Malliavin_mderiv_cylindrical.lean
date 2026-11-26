-- Prove2me | solution 1 for Malliavin.mderiv_cylindrical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:09.098303+00:00
-- url     : https://prove2.me/submissions/a4d6ad1e-9b68-4abd-b570-07c296991dde

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
import Theorems.Thm_Malliavin_CameronMartin_apply_inclusion
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
theorem _root_.solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (L : Fin n → StrongDual ℝ W)
    (x : W) (hf : DifferentiableAt ℝ f (fun i ↦ L i x)) :
    mderiv μ (fun y ↦ f (fun i ↦ L i y)) x =
      ∑ i, fderiv ℝ f (fun i ↦ L i x) (Pi.single i 1) • ofDual μ (L i) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_mderiv, Submodule.coe_inner, Submodule.coe_sum, sum_inner]
  simp only [Submodule.coe_smul, real_inner_smul_left]
  simp_rw [← Submodule.coe_inner, ← apply_inclusion]
  set Λ : W →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.pi L with hΛ
  have hcomp : (fun y ↦ f (fun i ↦ L i y)) = f ∘ Λ := by
    funext y
    simp only [hΛ, ContinuousLinearMap.coe_pi', Function.comp_apply]
  rw [hcomp, fderiv_comp x hf Λ.differentiableAt, ContinuousLinearMap.comp_apply, Λ.fderiv]
  have hpi : Λ (inclusion μ v) = ∑ i, L i (inclusion μ v) • (Pi.single i (1 : ℝ)) := by
    ext j
    simp only [hΛ, inclusion_apply, ContinuousLinearMap.coe_pi', Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hpi, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [inclusion_apply, hΛ, ContinuousLinearMap.coe_pi', mul_comm]
end Malliavin
