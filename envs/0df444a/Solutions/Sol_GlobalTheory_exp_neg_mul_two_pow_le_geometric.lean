-- Prove2me | solution 1 for GlobalTheory.exp_neg_mul_two_pow_le_geometric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:35:34.642704+00:00
-- url     : https://prove2.me/submissions/ca46e574-0d46-40e1-8f9f-55e79dbf0392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ShellSumElementaryInequalities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    Real.exp (-T * 2 ^ i) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by
  have hb : (1 : ℝ) + i ≤ 2 ^ i := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) i
    norm_num at h
    linarith
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) two_pos]
    linarith
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hexp : -T * 2 ^ i ≤ -T + (i : ℝ) * (-1) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ T by linarith) (sub_nonneg.mpr hb),
      mul_nonneg (sub_nonneg.mpr hT) hi]
  calc Real.exp (-T * 2 ^ i) ≤ Real.exp (-T + (i : ℝ) * (-1)) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-T) * Real.exp (-1) ^ i := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le he i) (Real.exp_pos _).le
end GlobalTheory
