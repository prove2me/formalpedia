-- Prove2me | solution 1 for KernelRamsey.ram_33
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:19:50.331462+00:00
-- url     : https://prove2.me/submissions/4c9b3ed3-5478-47dc-9c6f-2e2a1c6e05c8

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram_two_three
import Theorems.Thm_KernelRamsey_ram_step
open KernelRamsey Finset

theorem solution : Ram 3 6 := ram_step (t := 3) ram_two_three (by norm_num)
