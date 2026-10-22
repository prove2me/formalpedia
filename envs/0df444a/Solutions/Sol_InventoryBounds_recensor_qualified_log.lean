-- Prove2me | solution 1 for InventoryBounds.recensor_qualified_log
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:28:05.774559+00:00
-- url     : https://prove2.me/submissions/f081d989-64de-4fff-80b8-fbe74d5c0257

import Mathlib
import Definitions.Def_InventoryBounds_Primitives
set_option autoImplicit false

theorem solution (d a b : ℝ) (hab : a ≤ b) :
    min (min d b) a = min d a := by
  rw [min_assoc, min_eq_right hab]
