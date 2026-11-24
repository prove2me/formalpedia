-- Prove2me | solution 1 for KernelRamsey.bound_r44
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:19:38.314851+00:00
-- url     : https://prove2.me/submissions/3d43e707-8022-4740-8888-2699856271ef

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
import Theorems.Thm_KernelRamsey_ramsey_avoidance
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution : ∃ G : SimpleGraph (Fin 17), G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4 := ramsey_avoidance rows_r44 (by decide +kernel) (by decide +kernel) (by decide +kernel)
