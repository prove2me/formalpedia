-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_1_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:38.828724+00:00
-- url     : https://prove2.me/submissions/29c6422c-ecda-42ae-8d5a-0fdfdfcefd09

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 1 (rows[4]!) = (-18686933965106262007505 / 939524096 : ℚ) := by
  decide +kernel
