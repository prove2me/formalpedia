-- Prove2me | solution 1 for KernelRamsey.ram2_44
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:21:28.052169+00:00
-- url     : https://prove2.me/submissions/d94dd681-6dda-4079-afd2-632e41c8c107

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram2_step
import Theorems.Thm_KernelRamsey_ram2_34
import Theorems.Thm_KernelRamsey_ram2_43
open KernelRamsey Finset

theorem solution : Ram2 4 4 18 := ram2_step (s := 4) (t := 4) (a := 9) (b := 9) (by norm_num) (by norm_num) (by norm_num) ram2_34
    ram2_43
