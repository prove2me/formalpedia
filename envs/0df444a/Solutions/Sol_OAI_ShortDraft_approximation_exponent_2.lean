-- Prove2me | solution 2 for OAI.ShortDraft.approximation_exponent
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:03:59.218741+00:00
-- url     : https://prove2.me/submissions/e1aef2bf-f57f-4d50-bebc-50be65bcbab3

import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : (2 : ℚ) - 11 / 30 = 49 / 30 := by
  norm_num
