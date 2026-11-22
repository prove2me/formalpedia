-- Prove2me | solution 1 for LongGapsBetweenPrimes.coverW_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:39.177836+00:00
-- url     : https://prove2.me/submissions/592f8824-4af4-4848-9395-b1ab0c0c11b5

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} (hL : 2 ≤ Real.log x) :
    2 * Real.log x ^ 2 < (coverW x : ℝ) := by
  have hfloor : Real.log x ^ 4 < (coverW x : ℝ) + 1 := Nat.lt_floor_add_one _
  nlinarith [sq_nonneg (Real.log x ^ 2 - 2)]
end LongGapsBetweenPrimes
