-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_K_pivs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:20:05.317181+00:00
-- url     : https://prove2.me/submissions/dc85e466-b323-4129-99d9-07dc1b68640c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mPl_mPl_IsPivs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a t : ℕ) (ha : a < v) (ht : t < v) :
    ∀ k, k < 484 → IsPiv (K S0 Si0 (1 - Pl a) (1 - Pl t)) k k := by
  have ha' : a < 1771 := by simpa [show v = 1771 from rfl] using ha
  have ht' : t < 1771 := by simpa [show v = 1771 from rfl] using ht
  exact K_mPl_mPl_IsPivs S0 Si0 FB0_S0_Si0 ha' ht'
