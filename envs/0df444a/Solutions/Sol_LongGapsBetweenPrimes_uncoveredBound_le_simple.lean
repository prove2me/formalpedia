-- Prove2me | solution 1 for LongGapsBetweenPrimes.uncoveredBound_le_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:56.109519+00:00
-- url     : https://prove2.me/submissions/98bab7ca-3936-4c27-8677-d8bd62e6e339

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_truncated_double_exponential_le
import Theorems.Thm_LongGapsBetweenPrimes_gramBound_le_simple
import Theorems.Thm_LongGapsBetweenPrimes_overlapBound_le_simple

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {n : ℕ} {M x β C : ℝ} (hx : 1 ≤ x)
    (hβ : 0 ≤ β) (hn : (n : ℝ) ≤ x) (hsize : (n : ℝ) * C ≤ x / 16)
    (hlog : 48 * Real.log x ≤ x * β) (hM : x ^ 4 ≤ M - 1) (hlogM : 1 ≤ Real.log M)
    (hgram : Real.exp (1 / x ^ 2) ≤ 5 / 4) :
    uncoveredBound n β C M (sieveD x) ≤ (5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2) / x ^ 6 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM' : x ^ 4 ≤ M := hM.trans (sub_le_self _ zero_le_one)
  have hM0 : 0 < M := (pow_pos hx0 4).trans_le hM'
  have hgram' := (gramBound_le_simple hx hn hM hlogM).trans hgram
  have hexp := truncated_double_exponential_le hx0 hβ hsize hlog
  have hover := overlapBound_le_simple hx0 hM'
  have hover0 : 0 ≤ 4 * Real.log (sieveD x) / (M * Real.log 2) := by
    rw [sieveD, Real.log_exp]
    positivity
  calc
    uncoveredBound n β C M (sieveD x) ≤
        (5 / 4) * (2 * C ^ 2 * (1 / x ^ 6) +
          2 * (1 / (Real.log 2 * x ^ 3)) ^ 2) := by
      unfold uncoveredBound
      rw [mul_assoc (2 * C ^ 2)]
      gcongr
      unfold sieveD
      positivity
    _ = _ := by ring
end LongGapsBetweenPrimes
