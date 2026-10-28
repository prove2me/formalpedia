-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_10_3_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:03:21.949851+00:00
-- url     : https://prove2.me/submissions/969455c9-d65c-4b13-997b-44d0bf51e5b1

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 10 3 7 = (-22680 : ℚ) := by
  decide +kernel
