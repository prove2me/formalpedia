-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Pc_low
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:57:14.140348+00:00
-- url     : https://prove2.me/submissions/c39d805f-35c5-48b4-a1f3-7bfe5f30c8a6

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem solution : Pc 0 = 0 := by simp [Pc]
