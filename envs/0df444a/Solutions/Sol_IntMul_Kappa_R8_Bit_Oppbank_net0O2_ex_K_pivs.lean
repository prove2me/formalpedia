-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_ex_K_pivs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:14:56.917204+00:00
-- url     : https://prove2.me/submissions/0caab8ba-cd69-45f3-905c-74a6b6c6a04b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_S0_Si0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_one_mPl_IsPivs
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (b : ℕ) (hb : b < v) :
    ∀ k, k < 22 → IsPiv (K S0 Si0 1 (1 - Pl b)) k k := by
  have hb' : b < 1771 := by simpa [show v = 1771 from rfl] using hb
  exact K_one_mPl_IsPivs S0 Si0 FB0_S0_Si0 hb'
