-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_9_9_5_s50
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T07:54:56.825702+00:00
-- url     : https://prove2.me/submissions/88992031-a20c-48de-aff0-6efbecaa302f

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI OAI.Laughlin.Certificate

theorem solution :
    Y 9 9 5 = (1717697222431419971099331/838860800000000000000 : ℚ) := by
  decide +kernel
