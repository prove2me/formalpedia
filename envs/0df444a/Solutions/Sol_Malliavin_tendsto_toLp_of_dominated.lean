-- Prove2me | solution 1 for Malliavin.tendsto_toLp_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:18:33.923437+00:00
-- url     : https://prove2.me/submissions/c36280c8-3f18-4752-aabd-362bb414cdd2

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
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
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
namespace Malliavin
theorem _root_.solution {f : ℕ → α → E} {g : α → E} (hf : ∀ n, MemLp (f n) 2 μ)
    (hg : MemLp g 2 μ) {bound : α → ℝ} (hbound : Integrable bound μ)
    (h : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ ^ 2 ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 = ∫ x, ‖f n x - g x‖ ^ 2 ∂μ := by
    intro n
    rw [norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (hf n), MemLp.coeFn_toLp hg,
      Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g)] with x h2 h3 h4
    rw [h4, Pi.sub_apply, h2, h3]
  have hint : Tendsto (fun n ↦ ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 (∫ _, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence bound
      (fun n ↦ ((hf n).1.sub hg.1).norm.pow 2) hbound (fun n ↦ (h n).mono fun x hx ↦ ?_)
      (hlim.mono fun x hx ↦ ?_)
    · rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · have := (tendsto_iff_norm_sub_tendsto_zero.mp hx).pow 2
      simpa using this
  rw [integral_zero] at hint
  have hsq : Tendsto (fun n ↦ ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnorm] using hint
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this
end Malliavin
