-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_ec_width1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:50:48.756437+00:00
-- url     : https://prove2.me/submissions/03da681e-122b-4719-a365-748f8ee79911
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_edge_count_eq_hist1
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

private theorem hist_mult_one :
    ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 1))).map (fun p => p.2)).sum = 221936407 := by
  decide

theorem solution :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 1))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 1))).map (fun p => p.2)).sum := by
  rw [hist_mult_one]
  exact net0O2_ec_edge_count_eq_hist1
