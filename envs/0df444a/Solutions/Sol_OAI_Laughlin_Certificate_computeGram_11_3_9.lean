-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_3_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:02:03.14136+00:00
-- url     : https://prove2.me/submissions/0a588eb1-7b14-4607-81da-b8f18592f52d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 3 9 = (0 : ℚ) := by
  decide +kernel
