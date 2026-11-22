-- Prove2me | solution 1 for LongGapsBetweenPrimes.sieveZ_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:19.538765+00:00
-- url     : https://prove2.me/submissions/1f3d4d16-bf56-4308-b179-bc79dcb37ca8

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} (hx : 2 ≤ x) : x ^ 4 ≤ (sieveZ x : ℝ) - 1 := by
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hx4 : 16 ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 4)]
  have hx6 : 4 * x ^ 4 ≤ x ^ 6 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg (x ^ 2))]
  unfold sieveZ
  nlinarith [Nat.lt_floor_add_one (x ^ 6)]
end LongGapsBetweenPrimes
