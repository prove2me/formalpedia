-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_pickE_oneRun
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:50:43.221165+00:00
-- url     : https://prove2.me/submissions/d29ae1fe-447e-4ae0-9e54-f02be8fe5d35

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMomExpand
open Matrix

theorem solution (r : ℕ) (q : Matrix (Fin 529) (Fin 529) ℚ)
    (h : ∃ e, PE q (oneRun r) e) :
    oneRun r (pickE (PE q (oneRun r))).runs := by
  have : PE q (oneRun r) (pickE (PE q (oneRun r))) := pickE_of_exists h
  exact this.2
