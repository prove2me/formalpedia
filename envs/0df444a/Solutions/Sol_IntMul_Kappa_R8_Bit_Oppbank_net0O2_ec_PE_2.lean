-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ec_PE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:14:48.644793+00:00
-- url     : https://prove2.me/submissions/ff100e2c-1b8c-4902-8bb1-781b5a994f1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_K_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_K_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_K_piv
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a s : ℕ) (ha : a < v) (hs : s < v) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (Pl a) (Pl s)) (oneRun 1) e :=
  oneRun1_of_piv (K S0 Si0 (Pl a) (Pl s))
    (net0O2_ec_K_idem a s ha hs)
    (net0O2_ec_K_rank a s ha hs)
    (net0O2_ec_K_piv a s ha hs)
