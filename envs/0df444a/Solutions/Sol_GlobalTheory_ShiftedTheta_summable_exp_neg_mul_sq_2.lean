-- Prove2me | solution 2 for GlobalTheory.ShiftedTheta.summable_exp_neg_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:15:06.727463+00:00
-- url     : https://prove2.me/submissions/2da06405-c1b4-4a0d-a2c4-a245eba1e515

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
import Theorems.Thm_GlobalTheory_ShiftedTheta_hasSum_int_inv_sq
import Theorems.Thm_GlobalTheory_ShiftedTheta_exp_neg_mul_sq_le

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually (hasSum_int_inv_sq.summable.mul_left (2 / c ^ 2)) ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_mul_sq_le hc hn
end GlobalTheory.ShiftedTheta
