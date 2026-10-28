-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_5_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:01:28.340582+00:00
-- url     : https://prove2.me/submissions/f861feea-362c-4f6b-b23c-fb72e794ea32

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 5 9 = (113400 : ℚ) := by
  decide +kernel
