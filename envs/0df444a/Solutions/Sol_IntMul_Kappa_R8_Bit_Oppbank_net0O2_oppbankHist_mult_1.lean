-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_oppbankHist_mult_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:25:24.732956+00:00
-- url     : https://prove2.me/submissions/173acc6e-9d28-490f-a304-bd4e1ea4ce31

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank
theorem solution :
    ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 1))).map (fun p => p.2)).sum = 221936407 := by
  decide
