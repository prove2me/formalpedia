-- Prove2me | solution 1 for GlobalTheory.Hk.integral_ellipse_width
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:52:06.441786+00:00
-- url     : https://prove2.me/submissions/f66d8906-7221-44ef-8cba-6161059c18d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount
import Theorems.Thm_GlobalTheory_Hk_integral_sqrt_one_sub_sq_wide

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution (α γ x a b : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hx : 0 < x)
    (ha : a ≤ -Real.sqrt (x / γ)) (hb : Real.sqrt (x / γ) ≤ b) :
    ∫ t in a..b, 2 * Real.sqrt ((x - γ * t ^ 2) / α) = Real.pi / Real.sqrt (α * γ) * x := by
  have hxγ : 0 < x / γ := div_pos hx hγ
  have hr : 0 < Real.sqrt (x / γ) := Real.sqrt_pos.mpr hxγ
  have hr2 : Real.sqrt (x / γ) ^ 2 = x / γ := Real.sq_sqrt hxγ.le
  have key : ∀ t : ℝ, 2 * Real.sqrt ((x - γ * t ^ 2) / α)
      = (2 * Real.sqrt (x / α)) * Real.sqrt (1 - (t / Real.sqrt (x / γ)) ^ 2) := by
    intro t
    have e : (x - γ * t ^ 2) / α = (x / α) * (1 - (t / Real.sqrt (x / γ)) ^ 2) := by
      rw [div_pow, hr2]
      field_simp
    rw [e, Real.sqrt_mul (div_nonneg hx.le hα.le)]
    ring
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun u => Real.sqrt (1 - u ^ 2)) hr.ne',
    integral_sqrt_one_sub_sq_wide]
  · rw [smul_eq_mul]
    have hs : Real.sqrt (x / α) * Real.sqrt (x / γ) = x / Real.sqrt (α * γ) := by
      rw [← Real.sqrt_mul (div_nonneg hx.le hα.le),
        show x / α * (x / γ) = x ^ 2 / (α * γ) by field_simp,
        Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx.le]
    calc 2 * Real.sqrt (x / α) * (Real.sqrt (x / γ) * (Real.pi / 2))
        = Real.pi * (Real.sqrt (x / α) * Real.sqrt (x / γ)) := by ring
      _ = Real.pi / Real.sqrt (α * γ) * x := by rw [hs]; ring
  · rw [div_le_iff₀ hr]; linarith
  · rw [le_div_iff₀ hr]; linarith
end GlobalTheory.Hk
