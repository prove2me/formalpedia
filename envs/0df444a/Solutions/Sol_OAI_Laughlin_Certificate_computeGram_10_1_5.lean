-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_10_1_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:02:57.401417+00:00
-- url     : https://prove2.me/submissions/34cc8b0d-598d-4c49-a334-389acda11f05

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 10 1 5 = (0 : ℚ) := by
  decide +kernel
