-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_23_3_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:02:03.479879+00:00
-- url     : https://prove2.me/submissions/27077adb-fe32-46a5-8027-8d726b4ab76e

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 23 3 17 = (0 : ℚ) := by
  decide +kernel
