-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_v_mul_wEnt
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:07:09.321521+00:00
-- url     : https://prove2.me/submissions/e9f00fae-b34a-4b5f-9831-53699193acf3

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankConsts
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank

theorem solution : v * wEnt = 6272882 := by
  decide
