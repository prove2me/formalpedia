-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.dimCF_of_ND
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:26:58.619338+00:00
-- url     : https://prove2.me/submissions/19c7fad4-03e1-4fac-b010-c49a0a2aad2d

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution {n : ℕ} (hn : 1773 + n < codeBound) :
    dimCF (1773 + n) = dimF n := by
  have hne0 : ¬ (1773 + n = 0) := by omega
  have hne1 : ¬ (1773 + n = 1) := by omega
  have hge : ¬ (1773 + n < 1773) := by omega
  simp only [dimCF, hne0, hne1, hge, ↓reduceIte]
  rw [Nat.add_sub_cancel_left]
