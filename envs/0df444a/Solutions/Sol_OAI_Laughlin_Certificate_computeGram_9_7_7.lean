-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_9_7_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:01:03.047385+00:00
-- url     : https://prove2.me/submissions/54b2f766-06f1-403a-be58-5f389be38b27

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 9 7 7 = (1260 : ℚ) := by
  decide +kernel
