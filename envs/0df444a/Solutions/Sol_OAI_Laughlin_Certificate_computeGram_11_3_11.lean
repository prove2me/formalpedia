-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_3_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:03:38.700895+00:00
-- url     : https://prove2.me/submissions/fd00b5d5-96f9-4d6a-a9cc-2c1cfff53b30

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 3 11 = (2494800 : ℚ) := by
  decide +kernel
