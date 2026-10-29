-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R3a
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:48:50.368913+00:00
-- url     : https://prove2.me/submissions/910f8ce9-0295-4e55-945e-dbe0d5963b94

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound9a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound9b
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound10a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound10b
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

theorem solution : ∀ n, 45000 ≤ n → n < 55000 → HasCentre (densSupG n) := by
  intro n hlo hhi
  have hbnd : ∀ i, (densSupG n).testBit i = true → i < 1771 := by
    intro i hi
    have hlt : densSupG n < 2 ^ 1771 := by
      by_cases h0 : n < 47500
      · exact CentBound9a.densSupG_lt_range n (by omega) h0
      ·
        by_cases h1 : n < 50000
        · exact CentBound9b.densSupG_lt_range n (by omega) h1
        ·
          by_cases h2 : n < 52500
          · exact CentBound10a.densSupG_lt_range n (by omega) h2
          ·
            exact CentBound10b.densSupG_lt_range n (by omega) (by omega)
    by_contra hge
    have : (densSupG n).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) (Nat.le_of_not_gt hge)))
    exact Bool.false_ne_true (this ▸ hi)
  have hcs : centredStar (densSupG n) (centF n) = true := by
    by_cases h0 : n < 47500
    · exact CentBound9a.centredStar_range n (by omega) h0
    ·
      by_cases h1 : n < 50000
      · exact CentBound9b.centredStar_range n (by omega) h1
      ·
        by_cases h2 : n < 52500
        · exact CentBound10a.centredStar_range n (by omega) h2
        ·
          exact CentBound10b.centredStar_range n (by omega) (by omega)
  have hc : centF n < 23 := by
    by_cases h0 : n < 47500
    · exact CentBound9a.centF_lt_range n (by omega) h0
    ·
      by_cases h1 : n < 50000
      · exact CentBound9b.centF_lt_range n (by omega) h1
      ·
        by_cases h2 : n < 52500
        · exact CentBound10a.centF_lt_range n (by omega) h2
        ·
          exact CentBound10b.centF_lt_range n (by omega) (by omega)
  exact hasCentre_of_centredStar hc hcs hbnd
