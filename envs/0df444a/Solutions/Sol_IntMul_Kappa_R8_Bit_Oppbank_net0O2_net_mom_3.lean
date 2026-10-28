-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_net_mom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:14:32.038542+00:00
-- url     : https://prove2.me/submissions/be1babeb-cce0-4b9c-a3bf-add95a4876e2
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
