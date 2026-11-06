-- Prove2me | solution 2 for OAI.ShortDraft.mean_square_exponent
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:04:20.235584+00:00
-- url     : https://prove2.me/submissions/cb453929-c926-423b-af92-80d2f687ffee

import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : (21 / 10 : ℚ) - 11 / 60 = 23 / 12 := by
  norm_num
