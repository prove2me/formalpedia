-- Prove2me | solution 1 for LongGapsBetweenPrimes.intervalError_le_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:32.052797+00:00
-- url     : https://prove2.me/submissions/706ff098-8a16-48bd-a31f-92fe3f880c39

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_exp_neg_nat_mul_log
import Theorems.Thm_LongGapsBetweenPrimes_sieveT_lower

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} (hx : 2 ≤ x) (hlog : 12 * Real.log x ≤ x) :
    16 * sieveD x ^ 6 / sieveT x ≤ 32 / x ^ 3 := by
  have hx0 : 0 < x := by linarith
  calc
    16 * sieveD x ^ 6 / sieveT x ≤ 16 * sieveD x ^ 6 / (Real.exp x / 2) := by
      gcongr
      exact sieveT_lower hx
    _ = 32 * Real.exp (-x / 4) := by
      rw [sieveD, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      calc
        _ = 32 * (Real.exp (6 * (x / 8)) / Real.exp x) := by ring
        _ = _ := by rw [← Real.exp_sub]; congr 1; congr 1; ring
    _ ≤ 32 * Real.exp (-(3 : ℝ) * Real.log x) := by
      gcongr
      linarith
    _ = 32 / x ^ 3 := by
      have he : Real.exp (-(3 : ℝ) * Real.log x) = 1 / x ^ 3 := by
        simpa only [Nat.cast_ofNat] using exp_neg_nat_mul_log hx0 3
      rw [he]
      ring
end LongGapsBetweenPrimes
