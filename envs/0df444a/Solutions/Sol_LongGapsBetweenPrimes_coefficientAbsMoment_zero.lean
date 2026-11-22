-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientAbsMoment_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:40.120807+00:00
-- url     : https://prove2.me/submissions/e5eba2f9-de49-4a11-ba43-d9ea3df56382

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_partial_cancellation

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : 1 < P) : coefficientAbsMoment P 0 = 1 := by
  have h := partial_cancellation hP {1}
    (by simpa using Nat.one_mem_divisors.mpr (by omega : P ≠ 0)) (by simp)
  simpa [coefficientAbsMoment, coefficient, Finset.sdiff_singleton_eq_erase] using h.symm
end LongGapsBetweenPrimes
