-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_of_nest
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:04:52.488977+00:00
-- url     : https://prove2.me/submissions/e2f068a7-67b3-4f96-9b55-ee157aeb9ee5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_sound
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_of_Le
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : nestOK o c = true) : Dm o c * Dm o c = Dm o c :=
  Dm_idem_of_Le ho hc (nest_sound ho hc h)
