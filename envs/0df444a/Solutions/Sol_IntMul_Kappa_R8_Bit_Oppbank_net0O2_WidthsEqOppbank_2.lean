-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_WidthsEqOppbank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:43:53.849218+00:00
-- url     : https://prove2.me/submissions/8516c555-e8b5-44ff-9e94-9f7a1648fba4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_oneRun
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oneRunV_oppbank
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMomExpand
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution : WidthsEqOppbank := by
  intro τ
  have hmap :
      net0O.edges.map (edgeMom τ) =
        net0O.edges.map fun e => oneRunV τ (e.runs.head?.map (·.2.2) |>.getD 0) := by
    refine List.map_congr_left fun e he => ?_
    obtain ⟨r, hr⟩ := net0O2_edges_oneRun e he
    obtain ⟨hpos, hlt, hrs⟩ := hr
    change edgeMom τ e =
      oneRunV τ ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0)
    simp only [edgeMom, hrs, headW]
  rw [hmap]
  exact net0O2_oneRunV_oppbank τ
