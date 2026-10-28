-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_WidthsEqOppbank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:10:29.359978+00:00
-- url     : https://prove2.me/submissions/491eb443-78a5-4a8e-8ed4-38343bdbdd16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_AllOneRun
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oneRunV_oppbank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_edges_ne_dfltE
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMomExpand

theorem solution : WidthsEqOppbank := by
  intro τ
  have hA : AllOneRun := net0O2_AllOneRun
  have hmap :
      net0O.edges.map (edgeMom τ) =
        net0O.edges.map fun e => oneRunV τ (e.runs.head?.map (·.2.2) |>.getD 0) := by
    refine List.map_congr_left fun e he => ?_
    have hne := net0O_edges_ne_dfltE e he
    rcases hA e he with hd | ⟨r, hr⟩
    · exact (hne hd).elim
    · obtain ⟨_, _, hrs⟩ := hr
      simp only [edgeMom, hrs, headW]
  rw [hmap]
  exact net0O2_oneRunV_oppbank τ
