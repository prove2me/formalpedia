-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:45.917332+00:00
-- url     : https://prove2.me/submissions/c36d0c63-c211-49a7-9142-c1713f81753d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 5 (rows[3]!) = (13068275739016009424895/16777216 : ℚ) := by
  decide +kernel
