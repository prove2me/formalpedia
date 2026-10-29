-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_1_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:05:36.686137+00:00
-- url     : https://prove2.me/submissions/e9942da3-b002-4ff0-9869-3958903f36f9

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 1 5 (rows[3]!) = (-24352127547028721893585 / 234881024 : ℚ) := by
  decide +kernel
