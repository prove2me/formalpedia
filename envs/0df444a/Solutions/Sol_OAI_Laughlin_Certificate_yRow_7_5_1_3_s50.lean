-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_5_1_3_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:30.099907+00:00
-- url     : https://prove2.me/submissions/bd0bd443-f0ec-4065-92b0-148660902f18

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 5 1 (rows[3]!) = (126559883614713029393025 / 117440512 : ℚ) := by
  decide +kernel
