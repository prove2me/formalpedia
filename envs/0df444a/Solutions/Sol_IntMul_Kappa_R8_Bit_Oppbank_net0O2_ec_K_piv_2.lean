-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ec_K_piv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:14:57.387626+00:00
-- url     : https://prove2.me/submissions/703e776c-2508-40da-bf26-793ca5961ff5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_Pl_Pl_IsPiv00
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a s : ℕ) (ha : a < v) (hs : s < v) :
    IsPiv (K S0 Si0 (Pl a) (Pl s)) 0 0 := by
  have ha' : a < 1771 := by simpa [show v = 1771 from rfl] using ha
  have hs' : s < 1771 := by simpa [show v = 1771 from rfl] using hs
  exact K_Pl_Pl_IsPiv00 S0 Si0 FB0_S0_Si0 ha' hs'
