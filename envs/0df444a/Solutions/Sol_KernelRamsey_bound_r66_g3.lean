-- Prove2me | solution 1 for KernelRamsey.bound_r66_g3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:59:31.722476+00:00
-- url     : https://prove2.me/submissions/481832ae-a471-4b22-bf7b-f4b8c47407b0

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 40 → 30 ≤ p →
      noClique (rows_r66) p 5 ((2 ^ p - 1) &&& row (rows_r66) p) = true := by
  decide +kernel
