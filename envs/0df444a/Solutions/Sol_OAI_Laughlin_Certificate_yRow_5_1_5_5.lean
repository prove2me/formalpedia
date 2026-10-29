-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:44.081615+00:00
-- url     : https://prove2.me/submissions/95e6a06a-6443-4166-bef7-cccdd6d926dc

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 1 5 (rows[5]!) = (209580109115659324643705 / 3758096384 : ℚ) := by
  decide +kernel
