-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.nest_Le_ND
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:07:41.351282+00:00
-- url     : https://prove2.me/submissions/a255be3a-133a-424b-9912-2cb7f32dcedc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_ND
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_NDpt
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_nest_Le_ND_PTnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution :
    ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
      ¬ o ≤ 1 → ¬ c ≤ 1 → dimCF o ≤ dimCF c → Le (Pc o) (Pc c) := by
  intro o c ho hc hnest ho1 hc1 hdim
  have hoble : Nat.ble o 1 = false := Bool.eq_false_iff.2 fun h => ho1 (Nat.ble_eq.mp h)
  have hcble : Nat.ble c 1 = false := Bool.eq_false_iff.2 fun h => hc1 (Nat.ble_eq.mp h)
  have hn := hnest
  simp only [nestOK, hoble, hcble, Bool.false_or] at hn
  cases hNDo : isND o <;> cases hNDc : isND c
  · cases hPTo : isPT o <;> cases hPTc : isPT c <;> simp [hNDo, hNDc, hPTo, hPTc] at hn
  · cases hPTo : isPT o
    · simp [hNDo, hNDc, hPTo] at hn
    · exact nest_Le_ND_PTnd o c ho hc hnest hPTo hNDc hdim
  · cases hPTc : isPT c
    · simp [hNDo, hNDc, hPTc] at hn
    · exact nest_Le_ND_NDpt o c ho hc hnest hNDo hPTc hdim
  · exact nest_Le_ND_ND o c ho hc hnest hNDo hNDc hdim
