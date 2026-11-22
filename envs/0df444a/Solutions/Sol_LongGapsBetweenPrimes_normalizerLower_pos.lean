-- Prove2me | solution 1 for LongGapsBetweenPrimes.normalizerLower_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:40:51.7258+00:00
-- url     : https://prove2.me/submissions/3ad20265-1240-45ee-b8e5-2fa80cf83880

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : 0 < normalizerLower := by
  unfold normalizerLower
  positivity
end LongGapsBetweenPrimes
