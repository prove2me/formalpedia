-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:48.6756+00:00
-- url     : https://prove2.me/submissions/eae2edd5-2fbc-4a49-8e83-d501e286485e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 3 (rows[2]!) = (4154519314999427044985 / 469762048 : ℚ) := by
  decide +kernel
