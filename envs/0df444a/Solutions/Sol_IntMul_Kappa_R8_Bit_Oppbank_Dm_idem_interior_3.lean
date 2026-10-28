-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_interior
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:00.881745+00:00
-- url     : https://prove2.me/submissions/fee33440-12e9-4375-ad36-8dd3a285758e
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

theorem solution :
    ∀ o c, o < SupG.codeBound → c < SupG.codeBound → nestOK o c = true →
      ¬ o ≤ 1 → ¬ c ≤ 1 → Dm o c * Dm o c = Dm o c := by
  intro o c ho hc hn _ _
  have ho' : o < codeBound := ho
  have hc' : c < codeBound := hc
  by_cases hdim : dimCF o ≤ dimCF c
  · exact Dm_idem_le ho' hc' (nest_Le_of_dim o c ho' hc' hn hdim) hdim
  · have hdim' : dimCF c ≤ dimCF o := Nat.le_of_not_ge hdim
    have hnest' : nestOK c o = true := by
      rw [← nestOK_symm o c]; exact hn
    exact Dm_idem_ge ho' hc' (nest_Le_of_dim c o hc' ho' hnest' hdim') hdim
