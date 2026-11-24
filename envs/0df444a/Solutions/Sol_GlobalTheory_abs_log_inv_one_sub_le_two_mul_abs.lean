-- Prove2me | solution 1 for GlobalTheory.abs_log_inv_one_sub_le_two_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:09.430679+00:00
-- url     : https://prove2.me/submissions/903c9d68-266c-4171-ae22-13b73d022c5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsLogInvOneSubLeTwoMulAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (y : ℝ) (hy : |y| ≤ 1 / 2) :
    |Real.log (1 - y)⁻¹| ≤ 2 * |y| := by
  have h1 := le_abs_self y
  have h2 := neg_abs_le y
  have h0 := abs_nonneg y
  have hpos : 0 < 1 - y := by linarith
  rw [abs_le]
  constructor
  · rw [Real.log_inv]
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h3 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have h4 : (1 - y)⁻¹ ≤ 1 + 2 * |y| := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith [mul_nonneg h0 (show (0:ℝ) ≤ |y| - y by linarith), mul_nonneg h0 (show (0:ℝ) ≤ 1 / 2 - |y| by linarith)]
    linarith
end GlobalTheory
