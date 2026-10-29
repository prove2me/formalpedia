-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_3_1_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:17.331811+00:00
-- url     : https://prove2.me/submissions/fe8f498e-91bf-4f28-9eec-9bd76b8d553f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 3 1 (rows[2]!) = (3609794378028611869977 / 1879048192 : ℚ) := by
  decide +kernel
