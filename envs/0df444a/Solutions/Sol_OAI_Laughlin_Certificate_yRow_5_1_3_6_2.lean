-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_1_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:05:33.808886+00:00
-- url     : https://prove2.me/submissions/d2c36760-2b25-4631-9fa4-cafa99df9e58

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 1 3 (rows[6]!) = (-26195139147988314471 / 8388608 : ℚ) := by
  decide +kernel
