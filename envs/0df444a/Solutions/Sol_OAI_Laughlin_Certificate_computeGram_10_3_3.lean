-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_10_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:03:14.139986+00:00
-- url     : https://prove2.me/submissions/1f4fa9f3-22a3-4dd7-8a96-c7d65916e0a2

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 10 3 3 = (30240 : ℚ) := by
  decide +kernel
