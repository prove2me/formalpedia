-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_tupleMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:37:00.971296+00:00
-- url     : https://prove2.me/submissions/32170cab-bd79-45ff-82a6-7dd110915e67

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_zero
import Theorems.Thm_LongGapsBetweenPrimes_sum_divisorIndex

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P k : ℕ) :
    (∑ r : DivisorTuple P k, tupleMass r) = coefficientMoment P 0 ^ k := by
  classical
  unfold tupleMass
  rw [← Fintype.prod_sum (fun (_ : Fin k) (d : DivisorIndex P) =>
    coefficient P d.val ^ 2 / (d.val.totient : ℝ))]
  rw [sum_divisorIndex P (fun d => coefficient P d ^ 2 / (d.totient : ℝ)),
    ← coefficientMoment_zero]
  simp
end LongGapsBetweenPrimes
