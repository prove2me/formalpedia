-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_of_nest
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:33.653823+00:00
-- url     : https://prove2.me/submissions/eb37d9a0-7677-45cc-9518-2ed409473c56
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
