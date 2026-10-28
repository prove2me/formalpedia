-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_e1_K_pivs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:55:54.582911+00:00
-- url     : https://prove2.me/submissions/a61c33e8-cf74-4978-ae4e-9170477a9eda
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_K_rank
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

theorem solution (b o c : ℕ) (hb : b < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    ∀ k, k < rkC o c → IsPiv (K S0 Si0 (Dm o c) (Pl b)) k k := by
  intro k hk
  exact IsPiv_diag_of_rank _ (rkC o c) (net0O2_e1_K_rank b o c hb ho hc hr)
    (rkC_lt_529 o c) k hk
