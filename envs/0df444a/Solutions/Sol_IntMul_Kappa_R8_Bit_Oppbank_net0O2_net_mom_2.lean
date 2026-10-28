-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_net_mom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:14:17.74603+00:00
-- url     : https://prove2.me/submissions/b3951829-7b92-4e12-83d9-ee8c8b4e013e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_AllOneRun
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_WidthsEqOppbank
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMomExpand
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (τ : ℝ) :
    (net0O.edges.map (EM τ)).sum = histMoment oppbankHist 529 τ :=
  net_mom_of_packs net0O2_AllOneRun net0O2_WidthsEqOppbank τ
