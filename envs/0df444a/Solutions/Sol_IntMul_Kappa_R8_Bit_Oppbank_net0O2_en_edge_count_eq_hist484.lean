-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_edge_count_eq_hist484
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:18:13.121979+00:00
-- url     : https://prove2.me/submissions/6d20abb3-a0a1-48f1-b65d-dba870a1c464
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_slots_count
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

theorem solution :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))).length =
      6272882 := by
  calc
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))).length
        = 1771 * 3542 := net0O2_en_slots_count
    _ = 6272882 := by decide
