-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.formalOK_net0O2_of_EOKO2_impl
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:02:02.169743+00:00
-- url     : https://prove2.me/submissions/633e6a77-3a7a-4f01-a24d-277dbc10e6a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_formalOK_labels_scalars_of_EOKO2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.QHNet (FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    FormalOK (m := 529) net0O N :=
  formalOK_labels_scalars_of_EOKO2 N h
