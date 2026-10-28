-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_9_1_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:01:11.681356+00:00
-- url     : https://prove2.me/submissions/3c46e7fb-cdff-44e5-9cdb-ae718d567f92

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 9 1 5 = (0 : ℚ) := by
  decide +kernel
