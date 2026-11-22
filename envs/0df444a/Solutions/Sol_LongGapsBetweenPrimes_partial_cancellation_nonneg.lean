-- Prove2me | solution 1 for LongGapsBetweenPrimes.partial_cancellation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:40.609825+00:00
-- url     : https://prove2.me/submissions/35859666-3e35-4c24-9eb5-f239cf099a94

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_partial_cancellation

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : 1 < P)
    (E : Finset ℕ) (hE : E ⊆ P.divisors) (h1 : 1 ∈ E) :
    0 ≤ ∑ d ∈ E, coefficient P d / d.totient := by
  rw [partial_cancellation hP E hE h1]
  positivity
end LongGapsBetweenPrimes
