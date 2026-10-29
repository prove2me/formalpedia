-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_stages_run
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:28:58.820292+00:00
-- url     : https://prove2.me/submissions/c2e1e052-9f65-4059-a65b-8983a80daf47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_sc_stages_run_of_blk
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open IntMul.Kappa.R6.Bit (scalarStepH)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1 blk2)
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (v : Fin 104719230 → ZMod 2) (w : Fin 104719230) :
    ((List.range 1771).flatMap (blk2 (toNB ch0O))).foldl scalarStepH
      (((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl scalarStepH
        (Sum.elim v fun _ => 0)) (.inl (net0O.ρ w)) = v w :=
  net0O2_sc_stages_run_of_blk (fun _ _ _ => trivial) (fun _ _ _ => trivial) v w
