-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_eq_pickE
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:05:31.287269+00:00
-- url     : https://prove2.me/submissions/87461b99-6347-437f-accb-8b5444919686

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix
theorem solution (a t : ℕ) (ha : a < v) (ht : t < v) :
    ch0O.en a t =
      OneRunNet2.pickE (OneRunNet2.PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484)) := by
  simp [ch0O, ha, ht]
