-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_oneRunV_sum_counts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:20:50.41616+00:00
-- url     : https://prove2.me/submissions/b2cf5566-644b-451c-b535-1c1f4d538743
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oneRunV_from_counts
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_counts
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2

theorem solution (τ : ℝ) :
    (net0O.edges.map fun e =>
        oneRunV τ ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0)).sum =
      (oppbankHist.map fun p => (p.2 : ℝ) * oneRunV τ p.1).sum :=
  net0O2_oneRunV_from_counts τ net0O2_headW_counts
