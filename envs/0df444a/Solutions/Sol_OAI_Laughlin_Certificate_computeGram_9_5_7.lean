-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_9_5_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:00:45.94133+00:00
-- url     : https://prove2.me/submissions/dad069f1-1f44-4913-b34e-0bc285513221

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 9 5 7 = (0 : ℚ) := by
  decide +kernel
