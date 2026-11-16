-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.densSup_land_mono_of_argRel_of_dim
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T09:17:07.301384+00:00
-- url     : https://prove2.me/submissions/dc518349-ba31-4efa-9660-350f8df807e0

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel_of_dim_R0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel_of_dim_R1
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel_of_dim_R2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel_of_dim_R3
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_densSup_land_mono_of_argRel_of_dim_R4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

private def arg0 (n : ℕ) : ℕ := Nat.land (argF n) 65535
private def arg1 (n : ℕ) : ℕ := Nat.shiftRight (argF n) 16

private theorem land_pair (n : ℕ) (hn : n < 62478) :
    ((!Nat.blt (dimF (arg0 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg0 n)) (densSupG n)) (densSupG (arg0 n))) = true) ∧
    ((!Nat.blt (dimF (arg1 n)) (dimF n) ||
      Nat.beq (Nat.land (densSupG (arg1 n)) (densSupG n)) (densSupG (arg1 n))) = true) := by
  by_cases h0 : n < 12500
  · simpa [arg0, arg1] using densSup_land_mono_of_argRel_of_dim_R0 n (by omega) h0
  · by_cases h1 : n < 25000
    · simpa [arg0, arg1] using densSup_land_mono_of_argRel_of_dim_R1 n (by omega) h1
    · by_cases h2 : n < 37500
      · simpa [arg0, arg1] using densSup_land_mono_of_argRel_of_dim_R2 n (by omega) h2
      · by_cases h3 : n < 50000
        · simpa [arg0, arg1] using densSup_land_mono_of_argRel_of_dim_R3 n (by omega) h3
        · simpa [arg0, arg1] using densSup_land_mono_of_argRel_of_dim_R4 n (by omega) hn

theorem solution (a n : ℕ)
    (ha : a < SupG.nNodes) (hn : n < SupG.nNodes)
    (h : argRel a n = true) (hd : dimF a < dimF n) :
    Nat.land (densSupG a) (densSupG n) = densSupG a := by
  have hn' : n < 62478 := by simpa [SupG.nNodes] using hn
  simp only [argRel, Bool.or_eq_true, Nat.beq_eq] at h
  have hblt : Nat.blt (dimF a) (dimF n) = true := Nat.blt_eq.mpr hd
  have hp := land_pair n hn'
  rcases h with rfl | rfl
  · have hr := hp.1
    have : Nat.blt (dimF (arg0 n)) (dimF n) = true := by simpa [arg0] using hblt
    simp only [this, Bool.not_true, Bool.false_or, Nat.beq_eq] at hr
    simpa [arg0] using hr
  · have hr := hp.2
    have : Nat.blt (dimF (arg1 n)) (dimF n) = true := by simpa [arg1] using hblt
    simp only [this, Bool.not_true, Bool.false_or, Nat.beq_eq] at hr
    simpa [arg1] using hr
