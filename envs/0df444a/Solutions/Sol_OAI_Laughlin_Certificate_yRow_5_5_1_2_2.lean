-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_5_1_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:16.36791+00:00
-- url     : https://prove2.me/submissions/69d6d2cb-acf7-4c9b-a0c2-b6d7ee92a91f

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 1 (rows[2]!) = (-39698825671225989422295 / 939524096 : ℚ) := by
  decide +kernel
