-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_7_5_6_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:55.673014+00:00
-- url     : https://prove2.me/submissions/04092323-9e46-4ffe-a009-87a9f185d302

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 7 5 (rows[6]!) = (21601964370283224165 / 4194304 : ℚ) := by
  decide +kernel
