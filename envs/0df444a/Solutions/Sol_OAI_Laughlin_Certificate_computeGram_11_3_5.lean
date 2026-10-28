-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_3_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:01:53.931225+00:00
-- url     : https://prove2.me/submissions/71059a9e-9323-4fb1-990d-79ba7d7e1c0a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 3 5 = (0 : ℚ) := by
  decide +kernel
