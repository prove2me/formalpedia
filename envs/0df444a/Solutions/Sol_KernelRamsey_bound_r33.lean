-- Prove2me | solution 1 for KernelRamsey.bound_r33
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:19:25.168213+00:00
-- url     : https://prove2.me/submissions/ad960561-6633-41ba-9364-2e9801ab2dc7

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
import Theorems.Thm_KernelRamsey_ramsey_avoidance
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution : ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := ramsey_avoidance rows_r33 (by decide +kernel) (by decide +kernel) (by decide +kernel)
