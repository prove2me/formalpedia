-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_of_Le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:05:57.84778+00:00
-- url     : https://prove2.me/submissions/b4c2d715-d7bf-4105-bb39-0b0752e38f5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_eq_of_Le_dimrev
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
    (h : Le (Pc o) (Pc c) ∨ Le (Pc c) (Pc o)) :
    Dm o c * Dm o c = Dm o c := by
  rcases h with hLe | hLe
  · by_cases hdim : dimCF o ≤ dimCF c
    · exact Dm_idem_le ho hc hLe hdim
    · -- Le (Pc o)(Pc c) but dim o > dim c ⇒ equal projectors
      have e : Pc o = Pc c := Pc_eq_of_Le_dimrev ho hc hLe (Nat.le_of_not_ge hdim)
      unfold Dm
      rw [if_neg hdim, e, sub_self, Matrix.zero_mul]
  · by_cases hdim : dimCF o ≤ dimCF c
    · have e : Pc c = Pc o := Pc_eq_of_Le_dimrev hc ho hLe hdim
      unfold Dm
      rw [if_pos hdim, e, sub_self, Matrix.zero_mul]
    · exact Dm_idem_ge ho hc hLe hdim
