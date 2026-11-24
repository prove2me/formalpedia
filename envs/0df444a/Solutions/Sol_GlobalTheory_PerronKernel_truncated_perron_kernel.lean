-- Prove2me | solution 1 for GlobalTheory.PerronKernel.truncated_perron_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:07.735715+00:00
-- url     : https://prove2.me/submissions/95de3ae3-1692-4093-b2d1-2b20fe9c755f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_far_neg
import Theorems.Thm_GlobalTheory_PerronKernel_far_pos
import Theorems.Thm_GlobalTheory_PerronKernel_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel
namespace GlobalTheory.PerronKernel
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ y c T : ℝ, 0 < y → y ≠ 1 → 0 < c → 1 ≤ T → ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) - (if 1 < y then 1 else 0)‖ ≤ C * y ^ c * min 1 (1 / (T * |Real.log y|)) := by
  refine ⟨3, by norm_num, fun y c T hy hy1 hc hT => ?_⟩
  have hint : (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      = ∫ t in (-T)..T, cexp ((Real.log y : ℝ) * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), Complex.ofReal_log hy.le]
  rw [hint, Real.rpow_def_of_pos hy]
  set L := Real.log y with hLdef
  set V := ∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) with hV
  have hL : L ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hT0 : 0 < T := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hE : 0 < Real.exp (L * c) := Real.exp_pos _
  have hLa : 0 < |L| := abs_pos.mpr hL
  have hTL : 0 < T * |L| := mul_pos hT0 hLa
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hfar : ‖(1 / (2 * Real.pi) : ℂ) * V - (if 1 < y then 1 else 0)‖
      ≤ 1 / (2 * Real.pi) * (2 * Real.exp (L * c) / (T * |L|)) := by
    split_ifs with h1
    · have hLp : 0 < L := Real.log_pos h1
      have e : (1 / (2 * Real.pi) : ℂ) * V - 1 = (1 / (2 * Real.pi) : ℂ) * (V - 2 * Real.pi) := by
        have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
        field_simp
      rw [e, norm_mul, hn]
      exact mul_le_mul_of_nonneg_left (far_pos hLp hc hT0) (by positivity)
    · have hLn : L < 0 := Real.log_neg hy (lt_of_le_of_ne (not_lt.mp h1) hy1)
      rw [sub_zero, norm_mul, hn]
      exact mul_le_mul_of_nonneg_left (far_neg hLn hc hT0) (by positivity)
  have hind : ‖(if 1 < y then (1 : ℂ) else 0)‖ ≤ Real.exp (L * c) := by
    split_ifs with h1
    · rw [norm_one]
      exact Real.one_le_exp (mul_nonneg (Real.log_pos h1).le hc.le)
    · rw [norm_zero]
      exact hE.le
  have hnr : ‖(1 / (2 * Real.pi) : ℂ) * V - (if 1 < y then 1 else 0)‖
      ≤ 1 / (2 * Real.pi) * (Real.exp (L * c) * (Real.pi + 2 * (T * |L|))) + Real.exp (L * c) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, hn]
    exact add_le_add (mul_le_mul_of_nonneg_left (near L hc hT0) (by positivity)) hind
  rcases le_or_gt (T * |L|) 1 with hs | hs
  · rw [min_eq_left (by rw [le_div_iff₀ hTL]; linarith)]
    refine hnr.trans ?_
    have h2 : 1 / (2 * Real.pi) * (Real.exp (L * c) * (Real.pi + 2 * (T * |L|)))
        ≤ Real.exp (L * c) * 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hs hE.le, Real.pi_gt_three]
    linarith
  · rw [min_eq_right (by rw [div_le_iff₀ hTL]; linarith)]
    refine hfar.trans ?_
    rw [show 1 / (2 * Real.pi) * (2 * Real.exp (L * c) / (T * |L|))
        = 1 / Real.pi * (Real.exp (L * c) / (T * |L|)) by field_simp,
      show 3 * Real.exp (L * c) * (1 / (T * |L|)) = 3 * (Real.exp (L * c) / (T * |L|)) by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ hpi]
    nlinarith [Real.pi_gt_three]
end GlobalTheory.PerronKernel
