-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabFinal_of_EOKO2b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:11:16.160762+00:00
-- url     : https://prove2.me/submissions/29450a20-6061-4e0c-bced-c6ba1aac7890
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_LabFinal_of_EOKO2_core
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open AModel (swapMat)
open IntMul.Kappa.R6.Bit (labStepH)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    ∀ w, net0O.prog.foldl (labStepH N) (fun _ => 1) (.inl (net0O.ρ w)) = swapMat :=
  net0O2_LabFinal_of_EOKO2_core N h
