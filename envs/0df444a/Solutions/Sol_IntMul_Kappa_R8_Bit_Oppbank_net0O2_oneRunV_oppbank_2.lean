-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_oneRunV_oppbank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:13:41.460365+00:00
-- url     : https://prove2.me/submissions/9c86390a-1355-4127-aa5d-cf81a1b92368
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oneRunV_sum_counts
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2

theorem histMoment_oppbank_oneRunV (τ : ℝ) :
    histMoment oppbankHist 529 τ =
      (oppbankHist.map fun p => (p.2 : ℝ) * oneRunV τ p.1).sum := by
  unfold histMoment oneRunV fw
  rfl

theorem solution (τ : ℝ) :
    (net0O.edges.map fun e => oneRunV τ (e.runs.head?.map (·.2.2) |>.getD 0)).sum =
      histMoment oppbankHist 529 τ := by
  have h := net0O2_oneRunV_sum_counts τ
  -- LHS forms: sum_counts uses Option.map getD; target uses head?.map getD — defeq
  simpa [histMoment_oppbank_oneRunV τ] using h
