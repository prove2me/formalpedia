-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_3_1_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:05:35.909914+00:00
-- url     : https://prove2.me/submissions/fa1616d4-d90e-4123-bcb0-2b05f9fcc4ec

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 3 1 (rows[4]!) = (973139460225276068975 / 939524096 : ℚ) := by
  decide +kernel
