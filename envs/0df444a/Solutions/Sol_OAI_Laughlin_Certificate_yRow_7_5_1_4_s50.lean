-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_5_1_4_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:31.310495+00:00
-- url     : https://prove2.me/submissions/e82ef2ae-0957-4e16-8b57-8840b6e9b699

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 5 1 (rows[4]!) = (-46679206856806148273295 / 469762048 : ℚ) := by
  decide +kernel
