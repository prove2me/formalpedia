-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.norm_theta_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:30:41.357991+00:00
-- url     : https://prove2.me/submissions/d21f2a58-beb2-46c6-a8b2-4a89e15cb43d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_summable_nat_mul_exp_neg
import Theorems.Thm_GlobalTheory_Hk_LFam_norm_aChi_le

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
namespace LFam
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤
      (14 * ∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / 2 * n))) * 𝓕.B * Real.exp (-(t / 2)) := by
  have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
  have hs := (summable_nat_mul_exp_neg (t := 1 / 2) (by norm_num)).hasSum.mul_left
    (14 * 𝓕.B * Real.exp (-(t / 2)))
  refine (tsum_of_norm_bounded hs fun n => ?_).trans (le_of_eq (by ring))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := 𝓕.norm_aChi_le χ 0
    simpa using this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : Real.exp (-(t * n)) ≤ Real.exp (-(t / 2)) * Real.exp (-(1 / 2 * n)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))
      ≤ (14 * 𝓕.B * n) * (Real.exp (-(t / 2)) * Real.exp (-(1 / 2 * n))) := by
        gcongr; exact 𝓕.norm_aChi_le χ n
    _ = _ := by ring
end LFam
end GlobalTheory.Hk
