-- Prove2me | solution 3 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_PE
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:07:09.915469+00:00
-- url     : https://prove2.me/submissions/e9ced453-35cd-43dc-8d41-037d6d09aded
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_K_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_K_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_K_pivs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a t : ℕ) (ha : a < v) (ht : t < v) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484) e :=
  oneRun_of_pivs 484 (by decide) (by decide)
    (K S0 Si0 (1 - Pl a) (1 - Pl t))
    (net0O2_en_K_idem a t ha ht)
    (net0O2_en_K_rank a t ha ht)
    (net0O2_en_K_pivs a t ha ht)
