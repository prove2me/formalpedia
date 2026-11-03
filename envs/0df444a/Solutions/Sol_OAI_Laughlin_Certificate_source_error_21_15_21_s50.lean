-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_15_21_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:38.752506+00:00
-- url     : https://prove2.me/submissions/f3bc8ef2-9c09-41e1-8ada-221eaa45faa5

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 15 21 = (0 : ℚ) := by
  decide +kernel
