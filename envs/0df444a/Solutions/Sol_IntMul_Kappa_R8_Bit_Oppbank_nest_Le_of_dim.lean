-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.nest_Le_of_dim
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:03:38.454768+00:00
-- url     : https://prove2.me/submissions/6ea7b5e3-9da0-4007-85d6-07ca1f7f3218
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts5
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts5
open IntMul.Kappa.R8.Bit.Oppbank.DimBound
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
  intro o c ho hc hn hdim
  by_cases ho1 : o ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ho1 with rfl | rfl
    · exact Le_Pc0_left c
    · have h1 : dimCF (1 : ℕ) = 23 := by simp [dimCF]
      have hc1 : c = 1 := (dimCF_eq_23_iff hc).1 (by
        have hle := dimCF_le_23 hc
        omega)
      subst hc1
      refine ⟨?_, ?_⟩ <;> simp [Pc_high]
  by_cases hc1 : c ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc1 with rfl | rfl
    · have hdim0 : dimCF (0 : ℕ) = 0 := by simp [dimCF]
      have ho_dim : dimCF o = 0 := Nat.le_zero.mp (by omega)
      by_cases h0 : o = 0
      · exact (ho1 (by omega)).elim
      by_cases h1 : o = 1
      · subst h1; simp [dimCF] at ho_dim
      by_cases hPT : o < 1773
      · simp [dimCF, h0, h1, hPT] at ho_dim
      · have hn' : o - 1773 < SupG.nNodes := by
          change o - 1773 < 62478
          have : codeBound = 64251 := rfl
          omega
        have hpos := dimF_pos (o - 1773) hn'
        have : dimCF o = dimF (o - 1773) := by
          simp [dimCF, h0, h1, hPT]
        omega
    · exact Le_Pc1_right o
  exact nest_Le_ND o c ho hc hn ho1 hc1 hdim
