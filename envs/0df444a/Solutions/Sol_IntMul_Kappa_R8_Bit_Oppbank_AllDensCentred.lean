-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:54:08.77893+00:00
-- url     : https://prove2.me/submissions/80f7638a-adff-40db-ac0b-3f292c72ba7e

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R0
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R1
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R3a
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred_R3b
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution : ∀ n < SupG.nNodes, HasCentre (densSupG n) := by
  intro n hn
  change n < 62478 at hn
  by_cases h0 : n < 15000
  · exact AllDensCentred_R0 n h0
  · by_cases h1 : n < 30000
    · exact AllDensCentred_R1 n (by omega) h1
    · by_cases h2 : n < 45000
      · exact AllDensCentred_R2 n (by omega) h2
      · by_cases h3 : n < 55000
        · exact AllDensCentred_R3a n (by omega) h3
        · exact AllDensCentred_R3b n (by omega) hn
