-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_3_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:05:39.267681+00:00
-- url     : https://prove2.me/submissions/31f9d33a-3a51-4953-bc99-ebf4cac8135d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 3 5 (rows[1]!) = (9078017688703880489 / 117440512 : ℚ) := by
  decide +kernel
