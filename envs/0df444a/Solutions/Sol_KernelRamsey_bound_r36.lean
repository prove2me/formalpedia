-- Prove2me | solution 1 for KernelRamsey.bound_r36
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:19:35.488465+00:00
-- url     : https://prove2.me/submissions/2625421b-8a79-46f9-ba06-ea8fd6708547

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
import Theorems.Thm_KernelRamsey_ramsey_avoidance
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution : ∃ G : SimpleGraph (Fin 17), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 6 := ramsey_avoidance rows_r36 (by decide +kernel) (by decide +kernel) (by decide +kernel)
