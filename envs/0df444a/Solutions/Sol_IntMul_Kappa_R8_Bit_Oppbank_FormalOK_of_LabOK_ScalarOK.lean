-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.FormalOK_of_LabOK_ScalarOK
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:57:56.921466+00:00
-- url     : https://prove2.me/submissions/387fc94b-dfa7-4deb-82f9-8cd0dbd3cb66

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FormalOK_bridge_net0O
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_scalarStepM_fInit2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open IntMul.Kappa.R6.Bit.QHNet (FormalOK LabOK ScalarOK)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ)
    (hL : LabOK (m := 529) net0O N) (hS : ScalarOK (m := 529) (R := ZMod 2) net0O) :
    FormalOK (m := 529) net0O N :=
  FormalOK_bridge_net0O N hL.1 hL.2 (net0O_scalarStepM_fInit2 N hS)
