-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.EOKO_edgeMats_large3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:33:29.522553+00:00
-- url     : https://prove2.me/submissions/be8a3128-a8bd-4af2-a035-6cfe9ace6a0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO_oneRun_PE_families
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_EOKO_edgeMats_of_PE
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f,
      let N := q ^ f
      (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        edgeMat N (ch0NB.e1 b o c) = redM N (pswQ (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)))) ∧
      (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        edgeMat N (ch0NB.e2 a o c) = redM N (pswQ (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)))) ∧
      (∀ b < 1771, edgeMat N (ch0NB.ex b) = redM N (pswQ (K ch0NB.S ch0NB.Si 1 (1 - Pl b)))) ∧
      (∀ a < 1771, ∀ t < 1771, edgeMat N (ch0NB.en a t) =
        redM N (pswQ (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)))) ∧
      (∀ a < 1771, edgeMat N (ch0NB.ei a) = redM N (pswQ (K ch0NB.S ch0NB.Si (1 - Pl a) 1))) ∧
      (∀ a < 1771, ∀ s < 1771, edgeMat N (ch0NB.ec a s) =
        redM N (pswQ (K ch0NB.S ch0NB.Si (Pl a) (Pl s)))) :=
  EOKO_edgeMats_of_PE EOKO_oneRun_PE_families
