-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_e2_PE_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:38:49.345555+00:00
-- url     : https://prove2.me/submissions/3975b3c9-3dd2-4011-8033-1c79b0165bad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e2_K_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e2_K_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e2_K_pivs
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_rkC_lt_529
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a o c : ℕ) (ha : a < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (Pl a) (Dm o c)) (oneRun (rkC o c)) e :=
  oneRun_of_pivs (rkC o c) hr (rkC_lt_529 o c)
    (K S0 Si0 (Pl a) (Dm o c))
    (net0O2_e2_K_idem a o c ha ho hc hr)
    (net0O2_e2_K_rank a o c ha ho hc hr)
    (net0O2_e2_K_pivs a o c ha ho hc hr)
