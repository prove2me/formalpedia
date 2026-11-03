-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_17_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:38.522268+00:00
-- url     : https://prove2.me/submissions/104f774e-7399-4096-b069-6e18b75c7e71

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 17 17 = (0 : ℚ) := by
  decide +kernel
