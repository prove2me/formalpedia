-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_5_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:50.171013+00:00
-- url     : https://prove2.me/submissions/c932624b-d7ce-4c74-8ac9-e34ab878a331

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 5 17 = (0 : ℚ) := by
  decide +kernel
