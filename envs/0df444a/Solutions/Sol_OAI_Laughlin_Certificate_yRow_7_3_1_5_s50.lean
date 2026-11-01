-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_3_1_5_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:27.773808+00:00
-- url     : https://prove2.me/submissions/adaf02df-454c-4abf-afa1-b87fccb10ab0

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 3 1 (rows[5]!) = (-29217720453316236095145 / 939524096 : ℚ) := by
  decide +kernel
