-- Prove2me | solution 1 for KernelRamsey.bound_r66_g1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:59:29.12174+00:00
-- url     : https://prove2.me/submissions/3f28ab63-25ff-4a05-9a58-ccec6b5b3811

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 20 → 10 ≤ p →
      noClique (rows_r66) p 5 ((2 ^ p - 1) &&& row (rows_r66) p) = true := by
  decide +kernel
