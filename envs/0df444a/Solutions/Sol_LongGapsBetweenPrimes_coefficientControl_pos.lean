-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientControl_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:52.417794+00:00
-- url     : https://prove2.me/submissions/43f44522-2250-469f-a4e0-f669b3b3487d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_absoluteMomentBound_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {b : ℝ} (hb : 0 < b) : 0 < coefficientControl b :=
  div_pos (absoluteMomentBound_pos hb) hb
end LongGapsBetweenPrimes
