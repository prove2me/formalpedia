-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_8_7_5_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-31T19:29:13.760983+00:00
-- url     : https://prove2.me/submissions/2bf831a9-a7e9-4bca-a423-bdcc23d85bea

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 8 7 5 = (707573349496458024998847/3355443200000000000000 : ℚ) := by
  decide +kernel
