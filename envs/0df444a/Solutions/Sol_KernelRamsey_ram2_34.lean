-- Prove2me | solution 1 for KernelRamsey.ram2_34
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:49:06.774496+00:00
-- url     : https://prove2.me/submissions/96dbb40e-9f93-48a5-b543-e356a7e8bc29

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram_49
open KernelRamsey Finset

theorem solution : Ram2 3 4 9 := ram_49
