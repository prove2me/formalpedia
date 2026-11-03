-- Prove2me | solution 1 for LL_Decomp1537b.ell_le
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:11:34.226371+00:00
-- url     : https://prove2.me/submissions/1c45e9f7-9c22-478e-983d-aa97455ce28a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution {N r t : ℝ} (hN : 4 ≤ N) (hr : 1 ≤ r) (hrN : r ≤ N) (ht : |t| ≤ Real.sqrt N) :
    Real.log (r * (|t| + 2)) ≤ 2 * Real.log N := by
  have hN0 : 0 < N := by linarith
  have hr0 : 0 < r := by linarith
  have hsq := Real.sq_sqrt hN0.le
  have hsqrt := Real.sqrt_nonneg N
  have hsqrtHalf : Real.sqrt N ≤ N / 2 := by
    nlinarith [mul_nonneg hN0.le (show 0 ≤ N - 4 by linarith)]
  have htN : |t| + 2 ≤ N := by linarith
  have hprod : r * (|t| + 2) ≤ N ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left htN hr0.le
    have h2 := mul_le_mul_of_nonneg_right hrN hN0.le
    nlinarith
  have hleft : 0 < r * (|t| + 2) := mul_pos hr0 (by positivity)
  calc
    Real.log (r * (|t| + 2)) ≤ Real.log (N ^ 2) := Real.log_le_log hleft hprod
    _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num

#print axioms solution