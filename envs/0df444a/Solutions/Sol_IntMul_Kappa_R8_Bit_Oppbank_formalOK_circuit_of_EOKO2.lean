-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.formalOK_circuit_of_EOKO2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:20:48.928577+00:00
-- url     : https://prove2.me/submissions/2333b216-efe1-4c06-9a9e-ed6f4cde6747
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_formalOK_net0O_of_EOKO_impl
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.QHNet (FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    FormalOK (m := 529) net0O N :=
  formalOK_net0O_of_EOKO_impl N h
