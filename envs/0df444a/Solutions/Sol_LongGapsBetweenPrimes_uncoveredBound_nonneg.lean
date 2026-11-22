-- Prove2me | solution 1 for LongGapsBetweenPrimes.uncoveredBound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:45:29.655807+00:00
-- url     : https://prove2.me/submissions/5ed7c0c6-74ea-4b66-9cfe-643cf6ecbcb9

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (k : ℕ) (β C M : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ uncoveredBound k β C M D := by unfold uncoveredBound gramBound; positivity
end LongGapsBetweenPrimes
