-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:47.485889+00:00
-- url     : https://prove2.me/submissions/60c107e9-30d2-434d-9032-f74fba4632b7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 3 (rows[2]!) = (36872577681837689686995/16777216 : ℚ) := by
  decide +kernel
