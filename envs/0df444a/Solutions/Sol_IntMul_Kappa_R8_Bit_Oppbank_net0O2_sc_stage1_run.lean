-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_stage1_run
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:04:56.059085+00:00
-- url     : https://prove2.me/submissions/1a3556d5-a664-402d-83fb-5c3127c34154

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (scalarStepH)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1)
theorem _root_.solution
    (vec : Fin 104719230 ⊕ Fin 3217907 → ZMod 2) :
    ((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl scalarStepH vec =
      ((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl scalarStepH vec := by rfl
end IntMul.Kappa.R8.Bit.Oppbank
