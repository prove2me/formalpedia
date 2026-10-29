-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:46.01505+00:00
-- url     : https://prove2.me/submissions/aa917250-c63f-4d9e-8121-45d8e4fda0fb

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 5 (rows[1]!) = (105906315909713386913 / 58720256 : ℚ) := by
  decide +kernel
