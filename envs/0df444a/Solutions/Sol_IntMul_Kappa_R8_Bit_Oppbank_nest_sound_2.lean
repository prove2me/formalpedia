-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.nest_sound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:07:00.052357+00:00
-- url     : https://prove2.me/submissions/e080c20c-0413-4d92-adb3-1c78e7ccbb95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nestOK_symm
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_of_dim
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : nestOK o c = true) :
    Le (Pc o) (Pc c) ∨ Le (Pc c) (Pc o) := by
  by_cases ho1 : o ≤ 1
  · exact nest_sound_low_o ho1 hc
  by_cases hc1 : c ≤ 1
  · exact nest_sound_low_c ho hc1
  by_cases hdim : dimCF o ≤ dimCF c
  · exact Or.inl (nest_Le_of_dim o c ho hc h hdim)
  · have hdim' : dimCF c ≤ dimCF o := Nat.le_of_not_ge hdim
    have hnest' : nestOK c o = true := by rw [← nestOK_symm o c]; exact h
    exact Or.inr (nest_Le_of_dim c o hc ho hnest' hdim')
