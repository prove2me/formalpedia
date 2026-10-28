-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_9_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:01:19.954988+00:00
-- url     : https://prove2.me/submissions/1abf3882-a241-4b50-b668-ac9b175f37b5

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 9 1 1 = (80640 : ℚ) := by
  decide +kernel
