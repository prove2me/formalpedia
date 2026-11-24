-- Prove2me | solution 1 for KernelRamsey.bound_r45
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:19:42.037358+00:00
-- url     : https://prove2.me/submissions/6ea2bf82-4eb9-4213-b698-f7d014d218a0

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
import Theorems.Thm_KernelRamsey_ramsey_avoidance
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution : ∃ G : SimpleGraph (Fin 24), G.CliqueFree 4 ∧ Gᶜ.CliqueFree 5 := ramsey_avoidance rows_r45 (by decide +kernel) (by decide +kernel) (by decide +kernel)
