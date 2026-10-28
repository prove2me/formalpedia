-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_mom_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:56:58.041996+00:00
-- url     : https://prove2.me/submissions/90f750da-80fb-41db-8527-0ce15f6aa33d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_hist_eq_oppbank
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution :
    ∀ τ : ℝ, histMoment net0O.hist 529 τ = histMoment bitR8 529 τ :=
  momEqO_of_hist_eq net0O2_hist_eq_oppbank
