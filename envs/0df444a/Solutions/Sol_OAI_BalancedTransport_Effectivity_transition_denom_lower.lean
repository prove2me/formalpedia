-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.transition_denom_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:50:40.091352+00:00
-- url     : https://prove2.me/submissions/164deecb-2c5a-4ac3-a484-015f5b1f08e2

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Polynomial


theorem solution (x : ℝ) :
    1 / 9 ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have hhalf : (1:ℝ)/9 ≤ expNegInvGlue (1/2) := by
    have h : expNegInvGlue (1/2) = Real.exp (-2) := by
      rw [expNegInvGlue, if_neg (by norm_num)]; norm_num
    rw [h, Real.exp_neg, show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have := Real.exp_one_lt_d9
    have hpos := Real.exp_pos 1
    rw [div_le_iff₀ (by norm_num), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    nlinarith
  rcases le_total (1/2:ℝ) x with h | h
  · have := expNegInvGlue.monotone h
    linarith [expNegInvGlue.nonneg (1 - x)]
  · have := expNegInvGlue.monotone (show (1/2:ℝ) ≤ 1 - x by linarith)
    linarith [expNegInvGlue.nonneg x]

