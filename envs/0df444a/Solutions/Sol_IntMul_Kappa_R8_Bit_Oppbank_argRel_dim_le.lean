-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.argRel_dim_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:50:56.0623+00:00
-- url     : https://prove2.me/submissions/a7173306-4cad-48bf-92b1-46a8bd95a24f

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_argRel_dim_le_R0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_argRel_dim_le_R1
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_argRel_dim_le_R2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_argRel_dim_le_R3
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_argRel_dim_le_R4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

private def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
private def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16

private theorem dim_pair (n : ℕ) (hn : n < 62478) :
    dimF (arg0 n) ≤ dimF n ∧ dimF (arg1 n) ≤ dimF n := by
  by_cases h0 : n < 12500
  · simpa [arg0, arg1] using argRel_dim_le_R0 n (by omega) h0
  · by_cases h1 : n < 25000
    · simpa [arg0, arg1] using argRel_dim_le_R1 n (by omega) h1
    · by_cases h2 : n < 37500
      · simpa [arg0, arg1] using argRel_dim_le_R2 n (by omega) h2
      · by_cases h3 : n < 50000
        · simpa [arg0, arg1] using argRel_dim_le_R3 n (by omega) h3
        · simpa [arg0, arg1] using argRel_dim_le_R4 n (by omega) hn

theorem solution {a n : ℕ} (ha : a < nNodes) (hn : n < nNodes)
    (h : argRel a n = true) : dimF a ≤ dimF n := by
  have hn' : n < 62478 := by simpa [nNodes] using hn
  simp only [argRel, Bool.or_eq_true, Nat.beq_eq] at h
  have hp := dim_pair n hn'
  rcases h with rfl | rfl
  · simpa [arg0] using hp.1
  · simpa [arg1] using hp.2
