-- Prove2me | solution 2 for OAI.SharpPlanar.IntegerIntervals.piI_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-06T03:36:50.360441+00:00
-- url     : https://prove2.me/submissions/fa972be0-9d4f-4961-93c0-e8f91cfa1984

import Mathlib
import Definitions.Def_OAIQ098E031

open OAI SharpPlanar.IntegerIntervals

theorem solution : piI.Contains (Complex.I * Real.pi) := by
  have hp := Real.pi_gt_d20
  have hq := Real.pi_lt_d20
  have hpi : piBounds.Contains Real.pi := by
    norm_num [piBounds, RBox.Contains, precision]
    constructor <;> linarith
  constructor
  · norm_num [CBox.Contains, RBox.Contains, piI]
  · simpa [piI] using hpi
