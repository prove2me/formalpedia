-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:02:31.528993+00:00
-- url     : https://prove2.me/submissions/0480bfbf-8e19-4a86-ae02-e88eb6e98f23

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 1 1 = (7257600 : ℚ) := by
  decide +kernel
