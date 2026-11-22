-- Prove2me | solution 1 for LongGapsBetweenPrimes.coverLength_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:01.999836+00:00
-- url     : https://prove2.me/submissions/c345b9db-98c6-4479-9bb2-9769259c5db7

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (η x : ℝ) : coverLength η x = ⌊η * coverScale x⌋₊ := by
  simp only [coverLength, coverScale, mul_div_assoc, mul_assoc]
end LongGapsBetweenPrimes
