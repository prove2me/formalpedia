-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_5_3_6_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:38.143229+00:00
-- url     : https://prove2.me/submissions/e21de047-7dd0-43a2-8647-cfab4ad08a2e

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 5 3 (rows[6]!) = (-50552514240995949885 / 16777216 : ℚ) := by
  decide +kernel
