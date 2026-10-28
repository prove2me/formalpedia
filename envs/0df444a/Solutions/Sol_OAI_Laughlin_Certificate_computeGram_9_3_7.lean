-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_9_3_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:00:54.630994+00:00
-- url     : https://prove2.me/submissions/b9cd8485-0599-47d3-914f-0c944d725f66

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 9 3 7 = (0 : ℚ) := by
  decide +kernel
