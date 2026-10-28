-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_10_7_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:02:40.202091+00:00
-- url     : https://prove2.me/submissions/01959363-c6eb-4767-8b86-59e3cd5d725c

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 10 7 7 = (17010 : ℚ) := by
  decide +kernel
