-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_1_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:44.672249+00:00
-- url     : https://prove2.me/submissions/cfa00485-191b-4571-965e-35d6f3441c11

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 1 (rows[5]!) = (-347441421785295611479515/67108864 : ℚ) := by
  decide +kernel
