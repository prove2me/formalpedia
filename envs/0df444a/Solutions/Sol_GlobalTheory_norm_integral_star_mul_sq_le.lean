-- Prove2me | solution 1 for GlobalTheory.norm_integral_star_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:26:51.78225+00:00
-- url     : https://prove2.me/submissions/6f2e91dc-b9be-44d3-9478-f5f401c0219b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormIntegralStarMulSqLeMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hff : Integrable (fun x => star (f x) * f x) μ) (hhh : Integrable (fun x => star (h x) * h x) μ) :
    ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  have key : ∀ g : X → ℂ, (fun x => star (g x) * g x) = fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
    intro g; funext x; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re_eq : ∀ g : X → ℂ, (∫ x, star (g x) * g x ∂μ).re = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    intro g; rw [key g, integral_complex_ofReal]; rfl
  have int_sq : ∀ g : X → ℂ, Integrable (fun x => star (g x) * g x) μ → Integrable (fun x => ‖g x‖ ^ 2) μ := by
    intro g hg; rw [key g] at hg; have hr := hg.re; simp only [RCLike.re_to_complex, Complex.ofReal_re] at hr; exact hr
  have mf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hf).mpr (int_sq f hff)
  have mh : MemLp h (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hh).mpr (int_sq h hhh)
  have hold := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two mf mh
  simp only [Real.rpow_two] at hold
  rw [re_eq f, re_eq h]
  have A0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have B0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have n1 : ‖∫ x, star (f x) * h x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖h x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x; rw [norm_mul, norm_star]
  have n0 : 0 ≤ ‖∫ x, star (f x) * h x ∂μ‖ := norm_nonneg _
  have hsq : ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2
      = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖h x‖ ^ 2 ∂μ) := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt A0, Real.sq_sqrt B0]
  calc ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left₀ n0 (n1.trans hold) 2
    _ = _ := hsq
end GlobalTheory
