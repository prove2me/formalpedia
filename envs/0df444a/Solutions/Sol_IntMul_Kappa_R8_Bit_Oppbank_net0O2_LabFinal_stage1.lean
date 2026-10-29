-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabFinal_stage1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:05:21.081726+00:00
-- url     : https://prove2.me/submissions/3cf6d7e3-15da-4dc4-a840-92a2d077a155

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
open IntMul.Kappa.R6.Bit (labStepH FMat)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1)
theorem _root_.solution (N : ℕ) (h : EOKO ch0NB N) :
    ((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl (labStepH N) (fun _ => (1 : FMat 529 N)) =
      fun wr => ((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl (labStepH N) (fun _ => 1) wr := by rfl
end IntMul.Kappa.R8.Bit.Oppbank
