-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabOK_of_EOKO2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:55:45.430988+00:00
-- url     : https://prove2.me/submissions/8f0d5413-d304-4090-bf4f-1ecea1bf04cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_LabGates_of_EOKO2b
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_LabFinal_of_EOKO2b
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open IntMul.Kappa.R6.Bit.QHNet (LabOK)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    LabOK (m := 529) net0O N :=
  And.intro (net0O2_LabGates_of_EOKO2b N h) (net0O2_LabFinal_of_EOKO2b N h)
