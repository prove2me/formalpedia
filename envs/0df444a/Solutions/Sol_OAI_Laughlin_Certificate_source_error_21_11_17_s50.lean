-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_11_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T11:00:26.725897+00:00
-- url     : https://prove2.me/submissions/0fe5ecf7-9c3e-4a2a-ac1a-b0e2951335d5

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 21 11 17 = (0 : ℚ) := by
  decide +kernel
