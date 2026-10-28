-- Prove2me | solution 6 for IntMul.Kappa.R8.Bit.Oppbank.net0O_FormalOK_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:40:17.603898+00:00
-- url     : https://prove2.me/submissions/f27372f7-44d7-40da-91f6-e0fc37ec3b2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_EOK_large2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_formalOK_of_EOKO3
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.QHNet (FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f, FormalOK (m := 529) net0O (q ^ f) := by
  obtain ⟨q₀, hE⟩ := net0O_EOK_large2
  refine ⟨q₀, fun q hq hlt f => formalOK_of_EOKO3 (q ^ f) (hE q hq hlt f)⟩
