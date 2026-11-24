-- Prove2me | solution 1 for KernelRamsey.ram2_43
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:04:31.255461+00:00
-- url     : https://prove2.me/submissions/80e391bd-a354-494b-bbd8-40af6b78df03

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram2_symm
import Theorems.Thm_KernelRamsey_ram2_34
open KernelRamsey Finset

theorem solution : Ram2 4 3 9 := ram2_symm ram2_34
