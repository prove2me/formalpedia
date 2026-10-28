-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ei_PE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:20:02.05161+00:00
-- url     : https://prove2.me/submissions/247f6ea5-c8e7-4af8-86da-3bf00c23c7ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ei_K_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ei_K_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ei_K_pivs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a : ℕ) (ha : a < v) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22) e :=
  oneRun_of_pivs 22 (by decide) (by decide)
    (K S0 Si0 (1 - Pl a) 1)
    (net0O2_ei_K_idem a ha)
    (net0O2_ei_K_rank a ha)
    (net0O2_ei_K_pivs a ha)
