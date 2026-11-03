-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_9_5_3_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T07:54:30.829332+00:00
-- url     : https://prove2.me/submissions/2664228e-b412-4092-8039-d2d597dff358

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 9 5 3 = (-249132079557021880785303/11744051200000000000000 : ℚ) := by
  decide +kernel
