-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R3b
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:48:51.078578+00:00
-- url     : https://prove2.me/submissions/c3d362fa-3f5c-43f6-887d-40c87a893bdc

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound11
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound12
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_hasCentre_of_centredStar
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.Cent

theorem solution : ∀ n, 55000 ≤ n → n < 62478 → HasCentre (densSupG n) := by
  intro n hlo hhi
  have hbnd : ∀ i, (densSupG n).testBit i = true → i < 1771 := by
    intro i hi
    have hlt : densSupG n < 2 ^ 1771 := by
      by_cases h0 : n < 60000
      · exact CentBound11.densSupG_lt_range n (by omega) h0
      ·
        exact CentBound12.densSupG_lt_range n (by omega) (by omega)
    by_contra hge
    have : (densSupG n).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) (Nat.le_of_not_gt hge)))
    exact Bool.false_ne_true (this ▸ hi)
  have hcs : centredStar (densSupG n) (centF n) = true := by
    by_cases h0 : n < 60000
    · exact CentBound11.centredStar_range n (by omega) h0
    ·
      exact CentBound12.centredStar_range n (by omega) (by omega)
  have hc : centF n < 23 := by
    by_cases h0 : n < 60000
    · exact CentBound11.centF_lt_range n (by omega) h0
    ·
      exact CentBound12.centF_lt_range n (by omega) (by omega)
  exact hasCentre_of_centredStar hc hcs hbnd
