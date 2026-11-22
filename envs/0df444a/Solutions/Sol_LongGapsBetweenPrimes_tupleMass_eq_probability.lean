-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleMass_eq_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:45.82543+00:00
-- url     : https://prove2.me/submissions/fe9489b8-c5e5-414d-a7c4-e1239bf0e24e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_ge_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : P ≠ 0) (r : DivisorTuple P k) :
    tupleMass r = coefficientMoment P 0 ^ k * ∏ i, divisorProbability P (r i) := by
  have hA : coefficientMoment P 0 ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (coefficientMoment_ge_one hP 0))
  rw [mul_comm, ← div_eq_iff (pow_ne_zero k hA)]
  simp [tupleMass, divisorProbability, Finset.prod_div_distrib]
end LongGapsBetweenPrimes
