-- Prove2me | solution 1 for Malliavin.tendsto_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:33.083209+00:00
-- url     : https://prove2.me/submissions/f613e905-57e0-4550-8145-15c551c3caba

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
import Theorems.Thm_Malliavin_tendsto_div_nat_succ
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
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
universe u_1 u_2
open Malliavin
namespace Malliavin
theorem _root_.solution (x : ℝ) : Tendsto (fun n : ℕ ↦ cutoff n x) atTop (𝓝 x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [cutoff, zero_div, Real.arctan_zero, mul_zero, tendsto_const_nhds_iff]
  -- `cutoff n x = x * (arctan h / h)` with `h = x / (n + 1) → 0`
  have hslope : Tendsto (fun h : ℝ ↦ Real.arctan h / h) (𝓝[≠] 0) (𝓝 1) := by
    have := (Real.hasDerivAt_arctan 0).tendsto_slope_zero
    simp only [zero_add, Real.arctan_zero, sub_zero, smul_eq_mul] at this
    norm_num at this
    exact this.congr fun h ↦ by rw [inv_mul_eq_div]
  have hn : Tendsto (fun n : ℕ ↦ x / (n + 1 : ℝ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_div_nat_succ x, ?_⟩
    exact Filter.Eventually.of_forall fun n ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
  have h := (hslope.comp hn).const_mul x
  rw [mul_one] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply, cutoff]
  field_simp
end Malliavin
