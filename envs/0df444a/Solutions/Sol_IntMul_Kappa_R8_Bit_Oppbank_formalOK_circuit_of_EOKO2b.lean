-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.formalOK_circuit_of_EOKO2b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:00:07.15123+00:00
-- url     : https://prove2.me/submissions/c5e4b5e9-67a9-4353-a3c1-58e96d91daa9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_formalOK_net0O2_of_EOKO2_impl
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.QHNet (FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    FormalOK (m := 529) net0O N :=
  formalOK_net0O2_of_EOKO2_impl N h
