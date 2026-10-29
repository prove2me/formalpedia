-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabGates_of_EOKO2_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:42:58.624589+00:00
-- url     : https://prove2.me/submissions/c212716f-6137-4db1-bc28-16ecce14c97e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_LabGates_append
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_LabGates_stage1
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_LabGates_stage2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R6.Bit (LabGates)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1 blk2 prog)
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    LabGates N net0O.prog (fun _ => 1) := by
  have hprog : net0O.prog =
      (List.range 1771).flatMap (blk1 (toNB ch0O)) ++
        (List.range 1771).flatMap (blk2 (toNB ch0O)) := by
    simp only [net0O, NB.net, prog, List.range]
    -- v = 1771
    change (List.range v).flatMap (blk1 (toNB ch0O)) ++
        (List.range v).flatMap (blk2 (toNB ch0O)) =
      (List.range 1771).flatMap (blk1 (toNB ch0O)) ++
        (List.range 1771).flatMap (blk2 (toNB ch0O))
    simp only [show v = 1771 from rfl]
  rw [hprog]
  exact (LabGates_append _ _ (fun _ => 1)).2 ⟨net0O2_LabGates_stage1 N h, net0O2_LabGates_stage2 N h⟩
