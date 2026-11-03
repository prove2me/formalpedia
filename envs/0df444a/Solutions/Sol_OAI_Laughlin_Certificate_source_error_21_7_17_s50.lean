-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_7_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:55.739818+00:00
-- url     : https://prove2.me/submissions/bb014c62-aab3-4bd1-b15b-0e695d738011

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 7 17 = (0 : ℚ) := by
  decide +kernel
