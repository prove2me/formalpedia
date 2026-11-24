-- Prove2me | solution 1 for KernelRamsey.bound_r55
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:19:44.898803+00:00
-- url     : https://prove2.me/submissions/7807f532-1e00-4fc7-bca7-c787de48258b

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
import Theorems.Thm_KernelRamsey_ramsey_avoidance
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution : ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ Gᶜ.CliqueFree 5 := ramsey_avoidance rows_r55 (by decide +kernel) (by decide +kernel) (by decide +kernel)
