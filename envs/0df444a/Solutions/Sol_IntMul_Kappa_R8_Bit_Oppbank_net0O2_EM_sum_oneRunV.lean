-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_EM_sum_oneRunV
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:31:58.653121+00:00
-- url     : https://prove2.me/submissions/9a105080-622a-4bb1-9445-266118671833
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_oneRun
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (τ : ℝ) :
    (net0O.edges.map (EM τ)).sum =
      (net0O.edges.map fun e => oneRunV τ (e.runs.head?.map (·.2.2) |>.getD 0)).sum := by
  congr 1
  refine List.map_congr_left fun e he => ?_
  obtain ⟨r, hr⟩ := net0O2_edges_oneRun e he
  obtain ⟨hpos, hlt, hrs⟩ := hr
  have hEM : EM τ e = oneRunV τ r := EM_oneRun τ ⟨hpos, hlt, hrs⟩
  have hhd : (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = r := by
    rw [hrs, List.head?_cons, Option.map_some, Option.getD_some]
  change EM τ e = oneRunV τ ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0)
  exact hEM.trans (congrArg (oneRunV τ) hhd.symm)
