-- Prove2me | solution 1 for GlobalTheory.ShiftedTheta.shifted_theta_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:23.391537+00:00
-- url     : https://prove2.me/submissions/5822d03b-d903-481b-8359-3a0bc0a44f50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
import Theorems.Thm_GlobalTheory_ShiftedTheta_hasSum_int_inv_sq
import Theorems.Thm_GlobalTheory_ShiftedTheta_exp_neg_mul_sq_le
import Theorems.Thm_GlobalTheory_ShiftedTheta_summable_exp_neg_mul_sq
import Theorems.Thm_GlobalTheory_ShiftedTheta_summable_shifted
import Theorems.Thm_GlobalTheory_ShiftedTheta_poisson

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ShiftedTheta
namespace GlobalTheory.ShiftedTheta
theorem _root_.solution : ∀ s θ : ℝ, 0 < s → Summable (fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2))) ∧ |∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) - Real.sqrt (Real.pi / s)| ≤ Real.sqrt (Real.pi / s) * s ^ 2 := by
  intro s θ hs
  refine ⟨summable_shifted θ hs, ?_⟩
  set g : ℤ → ℂ := fun n =>
    cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) with hg
  have hpi := Real.pi_pos
  have hc : 0 < Real.pi ^ 2 / s := by positivity
  have hn : ∀ n : ℤ, ‖g n‖ = Real.exp (-(Real.pi ^ 2 / s * (n : ℝ) ^ 2)) := by
    intro n
    have e : -(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n
        = ((-(Real.pi ^ 2 / s * (n : ℝ) ^ 2) : ℝ) : ℂ) + ((-(2 * Real.pi * θ * n) : ℝ) : ℂ) * I := by
      push_cast
      ring
    simp only [hg]
    rw [e, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_exp_ofReal]
  have hsum : Summable g :=
    Summable.of_norm_bounded (summable_exp_neg_mul_sq hc) fun n => (hn n).le
  have hb : ‖∑' n : ℤ, if n = 0 then 0 else g n‖ ≤ 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) := by
    refine tsum_of_norm_bounded (hasSum_int_inv_sq.mul_left _) fun n => ?_
    split_ifs with h
    · rw [norm_zero]; positivity
    · rw [hn]; exact exp_neg_mul_sq_le hc h
  have hb2 : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) ≤ s ^ 2 := by
    have e : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) = s ^ 2 * (2 / (3 * Real.pi ^ 2)) := by
      field_simp
    rw [e]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hg0 : g 0 = 1 := by simp [hg]
  have hp := poisson θ hs
  change _ = _ * ∑' n, g n at hp
  rw [hsum.tsum_eq_add_tsum_ite 0, hg0] at hp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ofReal_sub, hp, mul_add, mul_one,
    add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hb.trans hb2) (Real.sqrt_nonneg _)
end GlobalTheory.ShiftedTheta
