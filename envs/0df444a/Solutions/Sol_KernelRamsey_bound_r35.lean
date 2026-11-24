-- Prove2me | solution 1 for KernelRamsey.bound_r35
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:19:32.421958+00:00
-- url     : https://prove2.me/submissions/a0cd5e1a-4850-4831-9a81-a3ef334ff391

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
import Theorems.Thm_KernelRamsey_ramsey_avoidance
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution : ∃ G : SimpleGraph (Fin 13), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5 := ramsey_avoidance rows_r35 (by decide +kernel) (by decide +kernel) (by decide +kernel)
