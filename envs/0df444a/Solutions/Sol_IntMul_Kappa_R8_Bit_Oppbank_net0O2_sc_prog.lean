-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_prog
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:11:16.87069+00:00
-- url     : https://prove2.me/submissions/bc19adaa-97b3-4d91-b64a-cd64d087657f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_sc_prog_of_blocks
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit (scalarStepH)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (v : Fin 104719230 → ZMod 2) (w : Fin 104719230) :
    net0O.prog.foldl scalarStepH (Sum.elim v fun _ => 0) (.inl (net0O.ρ w)) = v w :=
  net0O2_sc_prog_of_blocks (fun _ _ _ => trivial) (fun _ _ _ => trivial) v w
