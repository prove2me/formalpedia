-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O_scalarStepM_fInit2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:10:57.400819+00:00
-- url     : https://prove2.me/submissions/e6abe137-e23b-4655-a84f-2d155ddfc274

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_scalarOK_module_lift_net0O
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit (FMat FV scalarStepM)
open IntMul.Kappa.R6.Bit.QHNet (ScalarOK fInit)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ)
    (hS : ScalarOK (m := 529) (R := ZMod 2) net0O) (w : Fin 104719230) :
    net0O.prog.foldl (scalarStepM (R := ZMod 2) (M := FV (ZMod 2) (Fin 104719230) 529 N))
      (fInit (R := ZMod 2) (m := 529) N) (.inl (net0O.ρ w)) =
      Finsupp.single ((1 : FMat 529 N), w) 1 :=
  scalarOK_module_lift_net0O N hS w
