-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_1_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:51.236306+00:00
-- url     : https://prove2.me/submissions/2842cb4a-38f2-405c-8768-c3259082b90e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 1 (rows[5]!) = (209580109115659324643705 / 3758096384 : ℚ) := by
  decide +kernel
