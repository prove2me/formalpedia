-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_5_1_5_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:32.273626+00:00
-- url     : https://prove2.me/submissions/f89b4728-dcbb-41e6-b026-42e141492e6e

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 5 1 (rows[5]!) = (486363383031076447124835 / 1879048192 : ℚ) := by
  decide +kernel
