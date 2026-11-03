-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_23_1_13_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:01:45.319911+00:00
-- url     : https://prove2.me/submissions/9f72041c-e1c9-45cd-8e4f-a0df5813a5e2

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 23 1 13 = (0 : ℚ) := by
  decide +kernel
