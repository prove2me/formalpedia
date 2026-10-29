-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_5_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:50.506824+00:00
-- url     : https://prove2.me/submissions/221c779b-d896-40c3-a810-483f48b2f016

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 8 1 5 (rows[6]!) = (-177811778631486817125/8388608 : ℚ) := by
  decide +kernel
