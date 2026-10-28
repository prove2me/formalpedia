-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:38:24.532269+00:00
-- url     : https://prove2.me/submissions/3c0b7135-af47-456a-8b52-f47b5462be46

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNestBound
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.NestBound
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution :
    ∀ o c, o < SupG.codeBound → c < SupG.codeBound →
      o ≤ 1 ∨ c ≤ 1 → Dm o c * Dm o c = Dm o c :=
  fun o c ho hc h => Dm_idem_boundary (o := o) (c := c) ho hc h
