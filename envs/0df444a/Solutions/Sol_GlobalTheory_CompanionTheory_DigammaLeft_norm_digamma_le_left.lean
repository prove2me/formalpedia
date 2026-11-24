-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:45.906804+00:00
-- url     : https://prove2.me/submissions/c2949547-4fba-401a-9c59-0ff3b47aac91

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegion
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_digamma_sub_digamma_one_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_norm_cos_le_of_im
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_norm_cos_le_of_re
import Theorems.Thm_GlobalTheory_T_digamma_log_bound_right_half_plane


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLeft
namespace GlobalTheory.CompanionTheory.DigammaLeft
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 →
      (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) →
      ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.digamma_log_bound_right_half_plane
  refine ⟨2 * C + 10, by positivity, fun w hre halt => ?_⟩
  have hint : ∀ n : ℤ, w ≠ n := by
    intro n hn
    rcases halt with h | ⟨k, hk⟩
    · rw [hn] at h
      norm_num at h
    · have h1 : (n : ℝ) = (k : ℝ) / 2 + 1 / 4 := by
        rw [← hk, hn]; simp
      have h4 : (4 * n : ℝ) = 2 * k + 1 := by linarith
      have h5 : 4 * n = 2 * k + 1 := by exact_mod_cast h4
      omega
  have hcot : ‖Complex.cos (Real.pi * w)‖ ≤ 2 * ‖Complex.sin (Real.pi * w)‖ := by
    rcases halt with h | ⟨k, hk⟩
    · apply norm_cos_le_of_im
      have him : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp
      rw [him, abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    · apply norm_cos_le_of_re _ k
      simp [hk]
  have hcotn : ‖(Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)‖ ≤
      2 * Real.pi := by
    rcases eq_or_ne (Complex.sin (Real.pi * w)) 0 with h0 | h0
    · rw [h0]
      simp [Real.pi_pos.le]
    · have hpos : 0 < ‖Complex.sin (Real.pi * w)‖ := norm_pos_iff.mpr h0
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        div_le_iff₀ hpos]
      nlinarith [Real.pi_pos]
  have hrefl := digamma_sub_digamma_one_sub w hint
  have hdecomp : Complex.digamma w = Complex.digamma (1 - w) +
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by
    rw [← hrefl]; ring
  have hbd := hb (1 - w) (by simp; linarith)
  have hw0 := norm_nonneg w
  have hL : Real.log 2 ≤ Real.log (‖w‖ + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h1w : ‖1 - w‖ ≤ 1 + ‖w‖ := by simpa using norm_sub_le 1 w
  have hl2 : Real.log (‖1 - w‖ + 2) ≤ 2 * Real.log (‖w‖ + 2) := by
    have h2 : Real.log (‖1 - w‖ + 2) ≤ Real.log ((‖w‖ + 2) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at h2
  have hpi : 2 * Real.pi ≤ 10 * Real.log (‖w‖ + 2) := by
    linarith [Real.pi_lt_d2, Real.log_two_gt_d9]
  have hmul : C * Real.log (‖1 - w‖ + 2) ≤ C * (2 * Real.log (‖w‖ + 2)) :=
    mul_le_mul_of_nonneg_left hl2 hC.le
  calc ‖Complex.digamma w‖
      ≤ ‖Complex.digamma (1 - w)‖ +
          ‖(Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)‖ := by
        rw [hdecomp]
        simpa using norm_add_le (Complex.digamma (1 - w))
          (-((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)))
    _ ≤ (2 * C + 10) * Real.log (‖w‖ + 2) := by nlinarith
end GlobalTheory.CompanionTheory.DigammaLeft
