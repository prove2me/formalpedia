-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_13_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:26.72673+00:00
-- url     : https://prove2.me/submissions/74d6e4ed-b73c-4d82-aee7-ba06f7975c6a

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 13 17 = (0 : ℚ) := by
  decide +kernel
