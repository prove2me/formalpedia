-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_prog_of_chunk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:17:37.514679+00:00
-- url     : https://prove2.me/submissions/085c17b2-a6ab-44f6-b047-e8358cdea083
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_sc_of_stages
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_sc_stages_run
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open IntMul.Kappa.R6.Bit (scalarStepH)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution
    (h1 : ∀ (v : Fin 104719230 ⊕ Fin 3217907 → ZMod 2) (b : ℕ), b < 1771 → True)
    (h2 : ∀ (v : Fin 104719230 ⊕ Fin 3217907 → ZMod 2) (a : ℕ), a < 1771 → True) :
    ∀ (v : Fin 104719230 → ZMod 2) (w : Fin 104719230),
      net0O.prog.foldl scalarStepH (Sum.elim v fun _ => 0) (.inl (net0O.ρ w)) = v w :=
  net0O2_sc_of_stages (fun v w => net0O2_sc_stages_run v w)
