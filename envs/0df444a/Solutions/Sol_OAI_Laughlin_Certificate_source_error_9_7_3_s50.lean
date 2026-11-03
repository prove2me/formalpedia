-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_9_7_3_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T07:54:42.199753+00:00
-- url     : https://prove2.me/submissions/77f79004-c77d-4302-8384-554ab0aa3c1c

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 9 7 3 = (-172612848420190308157317/419430400000000000000 : ℚ) := by
  decide +kernel
