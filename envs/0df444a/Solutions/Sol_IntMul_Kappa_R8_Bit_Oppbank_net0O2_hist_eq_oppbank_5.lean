-- Prove2me | solution 5 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_hist_eq_oppbank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:40:17.046+00:00
-- url     : https://prove2.me/submissions/754df9b3-37fa-4a7c-8a2b-75747f8d5ac5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_EM_sum_oneRunV
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oneRunV_oppbank
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2

theorem solution : ∀ τ : ℝ, histMoment net0O.hist 529 τ = histMoment oppbankHist 529 τ := by
  intro τ
  calc
    histMoment net0O.hist 529 τ
        = (net0O.edges.map (EM τ)).sum := hist_mom_net0O τ
    _ = (net0O.edges.map fun e => oneRunV τ (e.runs.head?.map (·.2.2) |>.getD 0)).sum :=
          net0O2_EM_sum_oneRunV τ
    _ = histMoment oppbankHist 529 τ := net0O2_oneRunV_oppbank τ
