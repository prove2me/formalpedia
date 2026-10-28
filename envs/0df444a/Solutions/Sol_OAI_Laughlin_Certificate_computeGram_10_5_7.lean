-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_10_5_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:02:49.149431+00:00
-- url     : https://prove2.me/submissions/5d0cb4d5-d445-4fab-b3b0-87eeb7cd1a41

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 10 5 7 = (0 : ℚ) := by
  decide +kernel
