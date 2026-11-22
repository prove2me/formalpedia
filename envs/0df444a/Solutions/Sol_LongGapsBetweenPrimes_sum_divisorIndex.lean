-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_divisorIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:53.758066+00:00
-- url     : https://prove2.me/submissions/4aaede17-2a20-4dcf-940e-c8f13bdbbed8

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P : ℕ) (f : ℕ → ℝ) :
    (∑ d : DivisorIndex P, f d.val) = ∑ d ∈ P.divisors, f d := by
  exact Finset.sum_attach P.divisors f
end LongGapsBetweenPrimes
