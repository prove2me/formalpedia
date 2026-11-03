-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_5_21_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:50.343653+00:00
-- url     : https://prove2.me/submissions/098ec320-9907-4241-8045-a72619f8db13

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 5 21 = (0 : ℚ) := by
  decide +kernel
