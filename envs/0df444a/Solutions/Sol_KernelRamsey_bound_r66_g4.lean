-- Prove2me | solution 1 for KernelRamsey.bound_r66_g4
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:01:53.083671+00:00
-- url     : https://prove2.me/submissions/23d56b88-8d4c-4760-81d3-48f14ce796ef

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 50 → 40 ≤ p →
      noClique (rows_r66) p 5 ((2 ^ p - 1) &&& row (rows_r66) p) = true := by
  decide +kernel
