-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_7_7_5_4_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:02:53.245928+00:00
-- url     : https://prove2.me/submissions/31c68f8e-6b32-4d6e-87c8-5c2551d4b100

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001

open OAI OAI.Laughlin.Certificate

theorem solution :
    yRow 7 7 5 (rows[4]!) = (-3701247860527868239965 / 33554432 : ℚ) := by
  decide +kernel
