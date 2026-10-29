-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:40.880741+00:00
-- url     : https://prove2.me/submissions/9ab097b6-9e91-4266-9469-960ac1fabaa3

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 1 (rows[1]!) = (-75316015709295173739/8388608 : ℚ) := by
  decide +kernel
