-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_3_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:44.861753+00:00
-- url     : https://prove2.me/submissions/746c4a4c-39f5-483d-a51b-51231834dabc

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 3 (rows[0]!) = (-11387494346113586295/8192 : ℚ) := by
  decide +kernel
