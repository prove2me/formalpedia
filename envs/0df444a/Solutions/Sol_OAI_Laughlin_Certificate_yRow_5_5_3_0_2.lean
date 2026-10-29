-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_5_3_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:05:37.518061+00:00
-- url     : https://prove2.me/submissions/38def6c9-d489-42e8-a9cd-6ce01decc62c

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 3 (rows[0]!) = (2088880360412782875 / 8192 : ℚ) := by
  decide +kernel
