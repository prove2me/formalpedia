-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:17:42.644271+00:00
-- url     : https://prove2.me/submissions/5446c89c-e0ec-41a9-9bba-651fd34dc56a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_rank_PT
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_rank_ND
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution {c : ℕ} (hc : c < codeBound) : (Pc c).rank = dimCF c := by
  by_cases h0 : c = 0
  · subst h0; simp [Pc_low, dimCF, Matrix.rank_zero]
  by_cases h1 : c = 1
  · subst h1
    rw [Pc_high]
    have : (1 : Matrix (Fin 23) (Fin 23) ℚ).rank = Fintype.card (Fin 23) := Matrix.rank_one
    simp [dimCF, this]
  by_cases hPT : c < 1773
  · have h2 : 2 ≤ c := by omega
    have hr := Pc_rank_PT h2 hPT
    have hd : dimCF c = 22 := by simp [dimCF, h0, h1, hPT]
    rw [hr, hd]
  · set n := c - 1773
    have hn : 1773 + n < codeBound := by omega
    have hC := AllDensCentred n (by
      have hcb : codeBound = 64251 := rfl
      have hnn : nNodes = 62478 := rfl
      omega)
    have ec : c = 1773 + n := by omega
    have hr := Pc_rank_ND hn hC
    have hd : dimCF (1773 + n) = dimF n := by
      simp [dimCF, show ¬ (1773 + n = 1) by omega, show ¬ (1773 + n < 1773) by omega]
    rw [ec, hr, hd]
