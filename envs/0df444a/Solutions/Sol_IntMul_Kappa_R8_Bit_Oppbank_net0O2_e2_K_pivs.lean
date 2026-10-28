-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_e2_K_pivs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:55:55.53077+00:00
-- url     : https://prove2.me/submissions/648b30a6-f2a0-4c90-9aa2-c52b4d7f3ad6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e2_K_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_IsPiv_diag_of_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_rkC_lt_529
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a o c : ℕ) (ha : a < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    ∀ k, k < rkC o c → IsPiv (K S0 Si0 (Pl a) (Dm o c)) k k := by
  intro k hk
  exact IsPiv_diag_of_rank _ (rkC o c) (net0O2_e2_K_rank a o c ha ho hc hr)
    (rkC_lt_529 o c) k hk
