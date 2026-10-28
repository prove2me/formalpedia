-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeGram_11_7_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:01:36.494+00:00
-- url     : https://prove2.me/submissions/50a9140e-aa95-4432-956e-ff4112bfd473

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : GramCompute.ZFast 11 7 7 = (120960 : ℚ) := by
  decide +kernel
