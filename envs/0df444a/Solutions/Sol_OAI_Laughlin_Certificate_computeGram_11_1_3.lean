-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_1_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:02:12.503917+00:00
-- url     : https://prove2.me/submissions/30febbef-8caf-4d1d-8dfb-7013035d5e3e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 1 3 = (0 : ℚ) := by
  decide +kernel
