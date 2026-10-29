-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_width484_count_eq_entE_grid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:19:10.546451+00:00
-- url     : https://prove2.me/submissions/0d04d1cc-9bd8-44f1-a564-74e667743d46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_width484_edges_from_entI
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem solution :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))).length =
      ((List.range v).flatMap fun a =>
        (List.range wEnt).map fun w =>
          NB.entE (toNB ch0O) a w).length :=
  congrArg List.length net0O2_width484_edges_from_entI
