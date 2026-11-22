-- Prove2me | solution 1 for LongGapsBetweenPrimes.absoluteMomentBound_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:31.583487+00:00
-- url     : https://prove2.me/submissions/acec7ff7-dab8-47d7-aa40-26aeb0ebc514

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {b : ℝ} (hb : 0 < b) : 0 < absoluteMomentBound b := by
  unfold absoluteMomentBound
  positivity
end LongGapsBetweenPrimes
