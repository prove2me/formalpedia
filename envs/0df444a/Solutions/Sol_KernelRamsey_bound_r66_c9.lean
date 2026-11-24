-- Prove2me | solution 1 for KernelRamsey.bound_r66_c9
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:02:22.811077+00:00
-- url     : https://prove2.me/submissions/acba01a0-5fd0-4cf3-ba66-212674000d65

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 101 → 90 ≤ p →
      noClique (complementRows 101 rows_r66) p 5 ((2 ^ p - 1) &&& row (complementRows 101 rows_r66) p) = true := by
  decide +kernel
