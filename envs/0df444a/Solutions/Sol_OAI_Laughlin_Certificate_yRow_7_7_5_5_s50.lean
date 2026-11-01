-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_7_5_5_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:54.653749+00:00
-- url     : https://prove2.me/submissions/28b34b8f-368b-4ac2-a8e3-9cea128a0b0f

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 7 5 (rows[5]!) = (-111316765905740996833665 / 134217728 : ℚ) := by
  decide +kernel
