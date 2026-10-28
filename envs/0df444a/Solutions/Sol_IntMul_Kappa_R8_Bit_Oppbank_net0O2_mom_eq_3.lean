-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_mom_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:37:31.822757+00:00
-- url     : https://prove2.me/submissions/b07facd4-6c25-4896-acc4-1f62c25aba33
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
