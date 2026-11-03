-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_1_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:38.759321+00:00
-- url     : https://prove2.me/submissions/cd454968-a26e-4e70-9f64-7a57e8d043b2

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 1 17 = (0 : ℚ) := by
  decide +kernel
