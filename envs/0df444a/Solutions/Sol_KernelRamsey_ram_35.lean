-- Prove2me | solution 1 for KernelRamsey.ram_35
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:49:00.493003+00:00
-- url     : https://prove2.me/submissions/a049575c-773f-489d-9f53-533eb2754572

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram_step
import Theorems.Thm_KernelRamsey_ram_49
open KernelRamsey Finset

theorem solution : Ram 5 14 := ram_step (t := 5) ram_49 (by norm_num)
