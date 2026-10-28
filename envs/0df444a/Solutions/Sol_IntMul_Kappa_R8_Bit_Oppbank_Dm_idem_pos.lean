-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:53:17.107797+00:00
-- url     : https://prove2.me/submissions/249adaaf-9bf5-4512-a6c7-d80447e10eb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_of_nest
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nestOK_of_rkC_pos
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (o c : ℕ) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    Dm o c * Dm o c = Dm o c := by
  exact Dm_idem_of_nest ho hc (nestOK_of_rkC_pos ho hc hr)
