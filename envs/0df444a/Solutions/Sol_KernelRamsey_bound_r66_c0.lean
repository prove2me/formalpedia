-- Prove2me | solution 1 for KernelRamsey.bound_r66_c0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:01:55.944841+00:00
-- url     : https://prove2.me/submissions/a1980e89-e0c2-4a62-b120-828be54be9a6

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 10 → 0 ≤ p →
      noClique (complementRows 101 rows_r66) p 5 ((2 ^ p - 1) &&& row (complementRows 101 rows_r66) p) = true := by
  decide +kernel
