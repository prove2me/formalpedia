-- Prove2me | solution 1 for KernelRamsey.bound_r66_c7
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:02:17.450722+00:00
-- url     : https://prove2.me/submissions/944832a0-ef49-4987-a335-2cd4ce000e0a

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 80 → 70 ≤ p →
      noClique (complementRows 101 rows_r66) p 5 ((2 ^ p - 1) &&& row (complementRows 101 rows_r66) p) = true := by
  decide +kernel
