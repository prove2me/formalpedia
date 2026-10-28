-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ex_PE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:19:59.958989+00:00
-- url     : https://prove2.me/submissions/75ba01c5-727b-4325-965e-b6d2ac3656a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_K_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_K_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_K_pivs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (b : ℕ) (hb : b < v) :
    ∃ e, OneRunNet2.PE (K S0 Si0 1 (1 - Pl b)) (oneRun 22) e :=
  oneRun_of_pivs 22 (by decide) (by decide)
    (K S0 Si0 1 (1 - Pl b))
    (net0O2_ex_K_idem b hb)
    (net0O2_ex_K_rank b hb)
    (net0O2_ex_K_pivs b hb)
