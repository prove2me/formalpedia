-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_13_21_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:32.87142+00:00
-- url     : https://prove2.me/submissions/7f77b720-1e4f-4b4c-953d-2716fefb5b8a

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 13 21 = (0 : ℚ) := by
  decide +kernel
