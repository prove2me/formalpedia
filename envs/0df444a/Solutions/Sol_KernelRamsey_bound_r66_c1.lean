-- Prove2me | solution 1 for KernelRamsey.bound_r66_c1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:01:58.698805+00:00
-- url     : https://prove2.me/submissions/1f852dbf-ac56-42e1-bcc4-6245df8fb7ab

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 20 → 10 ≤ p →
      noClique (complementRows 101 rows_r66) p 5 ((2 ^ p - 1) &&& row (complementRows 101 rows_r66) p) = true := by
  decide +kernel
