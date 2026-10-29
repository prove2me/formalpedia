-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_oppbankHist_mult_22
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:25:25.269194+00:00
-- url     : https://prove2.me/submissions/f50954b6-4c7b-4eff-8b60-bc979c0b57a8

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank
theorem solution :
    ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 22))).map (fun p => p.2)).sum = 116886 := by
  decide
