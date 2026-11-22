-- Prove2me | solution 1 for LongGapsBetweenPrimes.overlapBound_le_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:19.073806+00:00
-- url     : https://prove2.me/submissions/49379f6e-e3f3-40b6-9902-2b44b782e37e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {M x : ℝ} (hx : 0 < x) (hM : x ^ 4 ≤ M) :
    4 * Real.log (sieveD x) / (M * Real.log 2) ≤ 1 / (Real.log 2 * x ^ 3) := by
  rw [sieveD, Real.log_exp]
  calc
    4 * (x / 8) / (M * Real.log 2) ≤ x / (x ^ 4 * Real.log 2) := by
      gcongr
      linarith
    _ = 1 / (Real.log 2 * x ^ 3) := by field_simp
end LongGapsBetweenPrimes
