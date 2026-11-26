-- Prove2me | solution 1 for Malliavin.tendsto_brownianLp_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:27:31.276511+00:00
-- url     : https://prove2.me/submissions/e597bf86-d513-4bb0-8668-6627537a31ca

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
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
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
variable {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Filter.Tendsto (fun n : ℕ ↦ brownianLp hB (t - t / (n + 2))) Filter.atTop
      (nhds (brownianLp hB t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n : ℕ, ‖brownianLp hB (t - t / (n + 2)) - brownianLp hB t‖ ^ 2
      = ((t : ℝ) - (t - t / (n + 2) : ℝ≥0)) := by
    intro n
    have hle : (t - t / (n + 2) : ℝ≥0) ≤ t := tsub_le_self
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_brownianLp, inner_brownianLp, inner_brownianLp, inner_brownianLp, min_self, min_self,
      min_eq_left (by exact_mod_cast hle), min_eq_right (by exact_mod_cast hle)]
    ring
  have hto : Filter.Tendsto
      (fun n : ℕ ↦ ((t : ℝ) - (t - t / (n + 2) : ℝ≥0))) Filter.atTop (nhds 0) := by
    have hval : ∀ n : ℕ, ((t : ℝ) - (t - t / (n + 2) : ℝ≥0)) = (t : ℝ) / (n + 2) := by
      intro n
      have hdiv : (t / (n + 2) : ℝ≥0) ≤ t := by
        apply div_le_self zero_le
        exact_mod_cast Nat.le_add_left 1 (n + 1)
      rw [NNReal.coe_sub hdiv, NNReal.coe_div]
      push_cast
      ring
    simp only [hval]
    have := Filter.Tendsto.div_atTop (f := fun _ : ℕ ↦ (t : ℝ))
      (g := fun n : ℕ ↦ ((n : ℝ) + 2)) tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    exact this
  have hnorm : Filter.Tendsto
      (fun n : ℕ ↦ ‖brownianLp hB (t - t / (n + 2)) - brownianLp hB t‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simp only [hsq]
    exact hto
  have h0 : Filter.Tendsto
      (fun n : ℕ ↦ ‖brownianLp hB (t - t / (n + 2)) - brownianLp hB t‖)
      Filter.atTop (nhds 0) := by
    have := hnorm.sqrt
    simp only [Real.sqrt_zero] at this
    refine this.congr fun n ↦ ?_
    rw [Real.sqrt_sq (norm_nonneg _)]
  exact h0
end Malliavin
