-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_oppbankHist_mult_484
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:25:25.824063+00:00
-- url     : https://prove2.me/submissions/9666b9db-dbb8-4ce9-8e04-2aef4539c66f

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank
theorem solution :
    ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 484))).map (fun p => p.2)).sum = 6272882 := by
  decide
