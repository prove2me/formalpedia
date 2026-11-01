-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_5_1_6_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:33.301985+00:00
-- url     : https://prove2.me/submissions/778b6156-d685-4dde-9d69-b2d9e4feb615

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 5 1 (rows[6]!) = (-620279821822140423225 / 33554432 : ℚ) := by
  decide +kernel
