-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_3_21_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:50.238145+00:00
-- url     : https://prove2.me/submissions/61ee1967-162d-4ff7-ac9d-e60054481a5e

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 3 21 = (0 : ℚ) := by
  decide +kernel
