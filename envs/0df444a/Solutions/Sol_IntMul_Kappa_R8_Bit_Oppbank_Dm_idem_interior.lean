-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_interior
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:47:00.032989+00:00
-- url     : https://prove2.me/submissions/74153e69-193c-4a5e-a893-e5291d0f032c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_of_nest
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution :
    ∀ o c, o < SupG.codeBound → c < SupG.codeBound → nestOK o c = true →
      ¬ o ≤ 1 → ¬ c ≤ 1 → Dm o c * Dm o c = Dm o c := by
  intro o c ho hc hn _ _
  exact Dm_idem_of_nest ho hc hn
