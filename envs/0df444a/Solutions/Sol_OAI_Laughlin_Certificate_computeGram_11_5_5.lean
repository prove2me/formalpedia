-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:01:44.710636+00:00
-- url     : https://prove2.me/submissions/69bd505c-7960-4889-ab96-fc67cf22b0aa

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 5 5 = (54000 : ℚ) := by
  decide +kernel
