-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientMoment_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:13.188044+00:00
-- url     : https://prove2.me/submissions/b60eb866-b784-464f-ac97-f22e778becdd

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P : ℕ) :
    coefficientMoment P 0 = ∑ d ∈ P.divisors, coefficient P d ^ 2 / d.totient := by
  simp [coefficientMoment]
end LongGapsBetweenPrimes
