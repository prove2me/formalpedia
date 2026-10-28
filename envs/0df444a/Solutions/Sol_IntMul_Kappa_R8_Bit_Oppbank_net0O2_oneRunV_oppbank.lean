-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_oneRunV_oppbank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:39:33.214426+00:00
-- url     : https://prove2.me/submissions/21d5e171-34c9-45fb-af5c-ff89fe8cc879
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
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (τ : ℝ) :
    (net0O.edges.map fun e => oneRunV τ (e.runs.head?.map (·.2.2) |>.getD 0)).sum =
      histMoment oppbankHist 529 τ := by
  change (net0O.edges.map fun e =>
      oneRunV τ ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0)).sum =
    histMoment oppbankHist 529 τ
  refine (net0O2_oneRunV_sum_counts τ).trans ?_
  simp only [histMoment, oneRunV, fw]
  rfl
