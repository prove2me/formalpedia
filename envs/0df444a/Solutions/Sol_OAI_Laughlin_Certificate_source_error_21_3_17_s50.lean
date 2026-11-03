-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_3_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:44.357259+00:00
-- url     : https://prove2.me/submissions/aebe0f5b-8152-4e2f-b05c-522d8a2fc271

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 3 17 = (0 : ℚ) := by
  decide +kernel
