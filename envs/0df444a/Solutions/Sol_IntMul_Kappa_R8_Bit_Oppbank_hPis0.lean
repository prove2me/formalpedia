-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.hPis0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:09:27.239449+00:00
-- url     : https://prove2.me/submissions/79059a97-f155-44be-bd53-4a84b2340326
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.


import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_hPis0_Dm
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank
theorem solution : ∀ A ∈ Pis0, A * A = A :=
  hPis0_of_Dm hPis0_Dm
