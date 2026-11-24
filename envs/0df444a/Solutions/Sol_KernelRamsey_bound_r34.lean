-- Prove2me | solution 1 for KernelRamsey.bound_r34
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:19:28.101423+00:00
-- url     : https://prove2.me/submissions/b1e76bfa-2b2e-434b-9a50-d363b451cff0

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
import Theorems.Thm_KernelRamsey_ramsey_avoidance
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution : ∃ G : SimpleGraph (Fin 8), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4 := ramsey_avoidance rows_r34 (by decide +kernel) (by decide +kernel) (by decide +kernel)
