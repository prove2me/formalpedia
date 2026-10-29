-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_5_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:15.270149+00:00
-- url     : https://prove2.me/submissions/01b752a4-d44b-4690-bc94-5b9f8c252604

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 5 5 (rows[3]!) = (16556987918363989467635 / 58720256 : ℚ) := by
  decide +kernel
