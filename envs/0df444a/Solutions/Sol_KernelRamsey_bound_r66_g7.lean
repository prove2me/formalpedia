-- Prove2me | solution 1 for KernelRamsey.bound_r66_g7
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:59:39.257041+00:00
-- url     : https://prove2.me/submissions/6edd4827-f283-4e72-92fa-5b55631b579c

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 80 → 70 ≤ p →
      noClique (rows_r66) p 5 ((2 ^ p - 1) &&& row (rows_r66) p) = true := by
  decide +kernel
