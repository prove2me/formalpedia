-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.formalOK_labels_scalars_of_EOKO2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:31:29.705746+00:00
-- url     : https://prove2.me/submissions/d7a6566b-ecd3-4a2f-8fe6-5ee0a53dd2c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_LabOK_of_EOKO2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ScalarOK
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FormalOK_of_LabOK_ScalarOK
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.QHNet (FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    FormalOK (m := 529) net0O N :=
  FormalOK_of_LabOK_ScalarOK N (net0O2_LabOK_of_EOKO2 N h) net0O2_ScalarOK
