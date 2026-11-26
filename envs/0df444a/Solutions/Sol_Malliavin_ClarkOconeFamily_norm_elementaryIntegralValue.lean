-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.norm_elementaryIntegralValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:18.127003+00:00
-- url     : https://prove2.me/submissions/8913286d-35ad-4cc9-991c-d2c447f61820

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_ClarkOconeFamily_coeFn_elementaryIntegralValue
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_wienerIntegral_indicatorConstLp_Ioc
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
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    ‖C.elementaryIntegralValue hab Z‖ = ‖iocIndicator a b‖ * ‖(Z : RandomL2 P)‖ := by
  let Δ : RandomL2 P := brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a
  have hΔcoe : (fun w ↦ B b w - B a w) =ᵐ[P] (Δ : W → ℝ) := by
    filter_upwards [Lp.coeFn_sub (brownianLp C.isPreBrownian b)
      (brownianLp C.isPreBrownian a), coeFn_brownianLp C.isPreBrownian b,
      coeFn_brownianLp C.isPreBrownian a] with w hsub hb ha
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hb, ha]
  have hindSq : IndepFun (fun w ↦ (Δ : W → ℝ) w ^ 2)
      (fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    ((C.indep_increment_adapted hab Z).congr hΔcoe Filter.EventuallyEq.rfl).comp
      (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hfactor := hindSq.integral_mul_eq_mul_integral
    (Lp.memLp Δ).integrable_sq.aestronglyMeasurable
    (Lp.memLp (Z : RandomL2 P)).integrable_sq.aestronglyMeasurable
  have hsq : ‖C.elementaryIntegralValue hab Z‖ ^ 2 =
      ‖Δ‖ ^ 2 * ‖(Z : RandomL2 P)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def,
      ← real_inner_self_eq_norm_sq Δ, L2.inner_def,
      ← real_inner_self_eq_norm_sq (Z : RandomL2 P), L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial, pow_two] at hfactor ⊢
    rw [← hfactor]
    apply integral_congr_ae
    filter_upwards [C.coeFn_elementaryIntegralValue hab Z, hΔcoe]
      with w hvalue hΔw
    rw [hvalue, hΔw]
    simp only [Pi.mul_apply]
    ring
  have hΔnorm : ‖Δ‖ = ‖iocIndicator a b‖ := by
    dsimp only [Δ]
    rw [← wienerIntegral_indicatorConstLp_Ioc C.isPreBrownian hab,
      norm_wienerIntegral]
    rfl
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [hsq, hΔnorm]
  ring
end ClarkOconeFamily
end Malliavin
