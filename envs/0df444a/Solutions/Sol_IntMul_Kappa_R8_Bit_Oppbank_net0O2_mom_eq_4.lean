-- Prove2me | solution 4 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_mom_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:01:09.869001+00:00
-- url     : https://prove2.me/submissions/3038a03c-0a78-41ec-b710-0167575a79b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_hist_eq_oppbank
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.MomPack

theorem solution : ∀ τ : ℝ, histMoment net0O.hist 529 τ = histMoment bitR8 529 τ := by
  intro τ
  calc
    histMoment net0O.hist 529 τ = histMoment oppbankHist 529 τ := net0O2_hist_eq_oppbank τ
    _ = histMoment bitR8 529 τ := histMoment_oppbank_bitR8_529 τ
