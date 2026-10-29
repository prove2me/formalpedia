-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:47.863207+00:00
-- url     : https://prove2.me/submissions/c8de6c64-e256-4f53-a507-4d21cce8d952

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 5 (rows[1]!) = (-18171099948981591081/2097152 : ℚ) := by
  decide +kernel
