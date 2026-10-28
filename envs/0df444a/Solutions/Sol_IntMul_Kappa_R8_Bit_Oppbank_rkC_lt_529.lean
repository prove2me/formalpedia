-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.rkC_lt_529
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:10:39.330063+00:00
-- url     : https://prove2.me/submissions/7669abae-2487-4306-a850-d46becb76b7f

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg

private theorem land_le_mask (x : ℕ) : Nat.land x 31 ≤ 31 := by
  simpa [Nat.land_eq] using (Nat.and_le_right : x &&& 31 ≤ 31)

private theorem shift5_mask : Nat.sub (Nat.shiftLeft 1 5) 1 = 31 := by decide

private theorem dimF_lt_32 (n : ℕ) : dimF n < 32 := by
  unfold dimF fieldOf
  rw [shift5_mask]
  exact Nat.lt_succ_of_le (land_le_mask _)

private theorem dimCF_lt_529 (c : ℕ) : dimCF c < 529 := by
  unfold dimCF
  split_ifs
  · omega
  · omega
  · omega
  · exact Nat.lt_trans (dimF_lt_32 (c - 1773)) (by decide : 32 < 529)

theorem solution (o c : ℕ) : rkC o c < 529 := by
  -- rkC = |dimCF o - dimCF c| ≤ max ≤ each < 529
  have ho := dimCF_lt_529 o
  have hc := dimCF_lt_529 c
  dsimp only [rkC]
  split_ifs with h
  · exact Nat.lt_of_le_of_lt (Nat.sub_le (dimCF c) (dimCF o)) hc
  · exact Nat.lt_of_le_of_lt (Nat.sub_le (dimCF o) (dimCF c)) ho
