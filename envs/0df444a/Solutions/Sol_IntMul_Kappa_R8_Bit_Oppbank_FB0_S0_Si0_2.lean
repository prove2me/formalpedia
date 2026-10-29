-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.FB0_S0_Si0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:26:49.63372+00:00
-- url     : https://prove2.me/submissions/b12a3e2d-4bb4-435b-8c18-83df25d71596
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_ex
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd

theorem solution : FB0 S0 Si0 := by
  have hEx : ∃ S, ∃ Sinv, FB0 S Sinv := by
    obtain ⟨S, Sinv, h⟩ := FB0_ex
    exact ⟨S, Sinv, h⟩
  have hS0 : ∃ Sinv, FB0 S0 Sinv := Classical.epsilon_spec hEx
  exact Classical.epsilon_spec hS0
