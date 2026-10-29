-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_3_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:03:43.5314+00:00
-- url     : https://prove2.me/submissions/3919151d-18da-438d-b1a5-0ddc806a3786

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : yRow 5 3 5 (rows[5]!) = (11113921888615690197695 / 939524096 : ℚ) := by
  decide +kernel
