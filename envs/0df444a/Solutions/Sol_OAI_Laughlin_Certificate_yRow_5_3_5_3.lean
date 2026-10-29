-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_3_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:18.202796+00:00
-- url     : https://prove2.me/submissions/351e5593-279a-4ce8-bead-6368e6d77822

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 3 5 (rows[3]!) = (-1676596742006268315615 / 117440512 : ℚ) := by
  decide +kernel
