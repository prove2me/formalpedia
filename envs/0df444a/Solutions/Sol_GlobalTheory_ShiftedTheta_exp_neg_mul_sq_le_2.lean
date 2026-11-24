-- Prove2me | solution 2 for GlobalTheory.ShiftedTheta.exp_neg_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:26.738829+00:00
-- url     : https://prove2.me/submissions/d131441a-89b4-4ff1-8f82-e7dc6d73f1d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
import Theorems.Thm_GlobalTheory_ShiftedTheta_exp_neg_le

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-(c * (n : ℝ) ^ 2)) ≤ 2 / c ^ 2 * (1 / (n : ℝ) ^ 2) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by
      have := sq_pos_of_ne_zero hn
      omega
    exact_mod_cast this
  refine (exp_neg_le (by positivity)).trans ?_
  rw [div_mul_div_comm, mul_one, mul_pow]
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  nlinarith
end GlobalTheory.ShiftedTheta
