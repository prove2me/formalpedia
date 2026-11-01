-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_5_3_3_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:35.190642+00:00
-- url     : https://prove2.me/submissions/c37ffdfd-9c58-47d7-be13-9bc873fd4410

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 5 3 (rows[3]!) = (-14416679890174213591545 / 58720256 : ℚ) := by
  decide +kernel
