-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ec_K_piv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:55:56.167822+00:00
-- url     : https://prove2.me/submissions/4f1c6e39-6948-4b43-bc04-3e23cf0c8945
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_K_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_IsPiv_diag_of_rank
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
  exact IsPiv_diag_of_rank _ 1 (net0O2_ec_K_rank a s ha hs) (by decide) 0 (by decide)
