-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_15_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:32.769394+00:00
-- url     : https://prove2.me/submissions/7fb7a1ab-66bc-4b54-8e03-3da698c66c0c

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 15 17 = (0 : ℚ) := by
  decide +kernel
