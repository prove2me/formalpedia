-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_from_PE_pack
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:37:01.449999+00:00
-- url     : https://prove2.me/submissions/6394385c-e702-43dd-aa1e-0043c7ea0b2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_fixed_widths
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_rkC_widths
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

theorem solution (w : ℕ) :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = w))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = w))).map (fun p => p.2)).sum := by
  by_cases h1 : w = 1
  · exact net0O2_headW_fixed_widths w (Or.inl h1)
  by_cases h22 : w = 22
  · exact net0O2_headW_fixed_widths w (Or.inr (Or.inl h22))
  by_cases h484 : w = 484
  · exact net0O2_headW_fixed_widths w (Or.inr (Or.inr h484))
  · exact net0O2_headW_rkC_widths w ⟨h1, h22, h484⟩
