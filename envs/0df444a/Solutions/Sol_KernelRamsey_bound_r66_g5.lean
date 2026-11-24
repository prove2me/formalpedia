-- Prove2me | solution 1 for KernelRamsey.bound_r66_g5
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:59:34.286903+00:00
-- url     : https://prove2.me/submissions/e31885f5-7cbd-45ee-8c7e-64b0d9b26d57

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution :
    ∀ p : Nat, p < 60 → 50 ≤ p →
      noClique (rows_r66) p 5 ((2 ^ p - 1) &&& row (rows_r66) p) = true := by
  decide +kernel
