-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_9_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:00:37.545136+00:00
-- url     : https://prove2.me/submissions/349d56b2-5627-4d4c-b923-4b4ee0e2b976

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 9 3 3 = (4320 : ℚ) := by
  decide +kernel
