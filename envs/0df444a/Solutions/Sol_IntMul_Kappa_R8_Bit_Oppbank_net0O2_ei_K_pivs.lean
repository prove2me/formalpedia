-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ei_K_pivs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:14:49.51775+00:00
-- url     : https://prove2.me/submissions/8658f170-d824-4601-9ccb-9a462dc1ab88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mPl_one_IsPivs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (a : ℕ) (ha : a < v) :
    ∀ k, k < 22 → IsPiv (K S0 Si0 (1 - Pl a) 1) k k := by
  have ha' : a < 1771 := by simpa [show v = 1771 from rfl] using ha
  exact K_mPl_one_IsPivs S0 Si0 FB0_S0_Si0 ha'
