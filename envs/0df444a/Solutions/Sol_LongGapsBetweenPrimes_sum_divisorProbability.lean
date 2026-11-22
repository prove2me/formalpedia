-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_divisorProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:16.219316+00:00
-- url     : https://prove2.me/submissions/20decba8-9c50-41c9-9738-361778c86363

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_zero
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_ge_one
import Theorems.Thm_LongGapsBetweenPrimes_sum_divisorIndex

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : P ≠ 0) :
    (∑ d : DivisorIndex P, divisorProbability P d) = 1 := by
  unfold divisorProbability
  rw [← Finset.sum_div,
    sum_divisorIndex P (fun d => coefficient P d ^ 2 / (d.totient : ℝ)),
    ← coefficientMoment_zero]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (coefficientMoment_ge_one hP 0)))
end LongGapsBetweenPrimes
