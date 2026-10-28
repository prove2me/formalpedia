-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_9_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:03:30.174247+00:00
-- url     : https://prove2.me/submissions/3fe3ea92-c0b8-4796-b167-279bf62e8bc9

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 9 11 = (-623700 : ℚ) := by
  decide +kernel
