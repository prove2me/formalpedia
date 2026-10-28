-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:40:50.663774+00:00
-- url     : https://prove2.me/submissions/bb2b4369-6c59-4049-a62c-58e2cd813006

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
