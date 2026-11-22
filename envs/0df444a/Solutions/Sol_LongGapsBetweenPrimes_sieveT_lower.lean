-- Prove2me | solution 1 for LongGapsBetweenPrimes.sieveT_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:20.027936+00:00
-- url     : https://prove2.me/submissions/e0eddedb-1efe-4b29-93c4-275db0a8e549

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} (hx : 2 ≤ x) : Real.exp x / 2 ≤ (sieveT x : ℝ) := by
  unfold sieveT
  linarith [Real.add_one_le_exp x, Nat.lt_floor_add_one (Real.exp x)]
end LongGapsBetweenPrimes
