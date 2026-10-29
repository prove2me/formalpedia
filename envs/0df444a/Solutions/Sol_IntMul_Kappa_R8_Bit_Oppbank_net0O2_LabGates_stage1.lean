-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabGates_stage1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:07:52.072098+00:00
-- url     : https://prove2.me/submissions/3e861ee1-237c-4e99-bfe6-43888bb9adf9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_LabGates_flatMap_prefix
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_LabGates_at_prefix
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R6.Bit (LabGates labStepH)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1)
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    LabGates N ((List.range 1771).flatMap (blk1 (toNB ch0O))) (fun _ => 1) :=
  LabGates_flatMap_prefix (blk := blk1 (toNB ch0O)) (L := fun _ => 1)
    (fun i hi => net0O2_blk1_LabGates_at_prefix N h i hi)
