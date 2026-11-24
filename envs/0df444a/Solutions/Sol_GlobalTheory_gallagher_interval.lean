-- Prove2me | solution 1 for GlobalTheory.gallagher_interval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:58:56.481022+00:00
-- url     : https://prove2.me/submissions/e33eee3a-9c64-4621-b89f-8c44477048b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (f f' h : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (hh : Continuous h) (hb : ∀ t, |f' t| ≤ h t) (x δ : ℝ) (hδ : 0 < δ) :
    f x ≤ ∫ t in x..(x + δ), (f t / δ + h t) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hF : ∀ t, HasDerivAt (fun t => (t - x - δ) / δ * f t) (f t / δ + (t - x - δ) / δ * f' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t - x - δ) / δ) (1 / δ) t :=
      (((hasDerivAt_id t).sub_const x).sub_const δ).div_const δ
    exact (h1.fun_mul (hf t)).congr_deriv (by ring)
  have hc : Continuous fun t => f t / δ + (t - x - δ) / δ * f' t := by fun_prop
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x + δ)
    (fun t _ => hF t) (hc.intervalIntegrable _ _)
  have h3 : (x + δ - x - δ) / δ * f (x + δ) - (x - x - δ) / δ * f x = f x := by
    field_simp
    ring
  rw [h3] at h2
  rw [← h2]
  apply intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t ht
  have h4 : |(t - x - δ) / δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hδ, div_le_one hδ, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h5 : (t - x - δ) / δ * f' t ≤ h t := by
    calc _ ≤ |(t - x - δ) / δ * f' t| := le_abs_self _
      _ = |(t - x - δ) / δ| * |f' t| := abs_mul _ _
      _ ≤ 1 * h t := mul_le_mul h4 (hb t) (abs_nonneg _) zero_le_one
      _ = h t := one_mul _
  linarith
end GlobalTheory
