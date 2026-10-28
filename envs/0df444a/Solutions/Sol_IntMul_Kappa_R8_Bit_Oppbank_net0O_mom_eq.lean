-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O_mom_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:06:16.267805+00:00
-- url     : https://prove2.me/submissions/5212942f-01c2-438f-8a5b-34097f247ece
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_hist_eq_oppbank
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution :
    ∀ τ : ℝ, histMoment net0O.hist 529 τ = histMoment bitR8 529 τ :=
  momEqO_of_hist_eq net0O_hist_eq_oppbank
