-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:48.749469+00:00
-- url     : https://prove2.me/submissions/65c2060c-6786-44f6-93d3-1f7709246ed2

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 3 (rows[4]!) = (-441299603451117593115/33554432 : ℚ) := by
  decide +kernel
