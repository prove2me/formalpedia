-- Prove2me | solution 1 for LongGapsBetweenPrimes.gramBound_le_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:17.685063+00:00
-- url     : https://prove2.me/submissions/ebca40ab-7c0a-48dc-9426-00c9073b6b33

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {n : ℕ} {M x : ℝ} (hx : 1 ≤ x) (hn : (n : ℝ) ≤ x)
    (hM : x ^ 4 ≤ M - 1) (hlog : 1 ≤ Real.log M) :
    gramBound n M (sieveD x) ≤ Real.exp (1 / x ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M - 1 := (pow_pos hx0 4).trans_le hM
  unfold gramBound sieveD
  rw [Real.log_exp]
  apply Real.exp_le_exp.mpr
  calc
    (n : ℝ) * (x / 8) / ((M - 1) * Real.log M) ≤ x * x / (x ^ 4 * 1) := by
      gcongr
      linarith
    _ = 1 / x ^ 2 := by field_simp
end LongGapsBetweenPrimes
