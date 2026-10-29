-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:36:46.926361+00:00
-- url     : https://prove2.me/submissions/2264b06c-82f6-4460-9a10-b5e49ce22fe3

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound6a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound6b
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound7a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound7b
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound8a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound8b
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

theorem solution : ∀ n, 30000 ≤ n → n < 45000 → HasCentre (densSupG n) := by
  intro n hlo hhi
  have hbnd : ∀ i, (densSupG n).testBit i = true → i < 1771 := by
    intro i hi
    have hlt : densSupG n < 2 ^ 1771 := by
      by_cases h0 : n < 32500
      · exact CentBound6a.densSupG_lt_range n (by omega) h0
      ·
        by_cases h1 : n < 35000
        · exact CentBound6b.densSupG_lt_range n (by omega) h1
        ·
          by_cases h2 : n < 37500
          · exact CentBound7a.densSupG_lt_range n (by omega) h2
          ·
            by_cases h3 : n < 40000
            · exact CentBound7b.densSupG_lt_range n (by omega) h3
            ·
              by_cases h4 : n < 42500
              · exact CentBound8a.densSupG_lt_range n (by omega) h4
              ·
                exact CentBound8b.densSupG_lt_range n (by omega) (by omega)
    by_contra hge
    have : (densSupG n).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) (Nat.le_of_not_gt hge)))
    exact Bool.false_ne_true (this ▸ hi)
  have hcs : centredStar (densSupG n) (centF n) = true := by
    by_cases h0 : n < 32500
    · exact CentBound6a.centredStar_range n (by omega) h0
    ·
      by_cases h1 : n < 35000
      · exact CentBound6b.centredStar_range n (by omega) h1
      ·
        by_cases h2 : n < 37500
        · exact CentBound7a.centredStar_range n (by omega) h2
        ·
          by_cases h3 : n < 40000
          · exact CentBound7b.centredStar_range n (by omega) h3
          ·
            by_cases h4 : n < 42500
            · exact CentBound8a.centredStar_range n (by omega) h4
            ·
              exact CentBound8b.centredStar_range n (by omega) (by omega)
  have hc : centF n < 23 := by
    by_cases h0 : n < 32500
    · exact CentBound6a.centF_lt_range n (by omega) h0
    ·
      by_cases h1 : n < 35000
      · exact CentBound6b.centF_lt_range n (by omega) h1
      ·
        by_cases h2 : n < 37500
        · exact CentBound7a.centF_lt_range n (by omega) h2
        ·
          by_cases h3 : n < 40000
          · exact CentBound7b.centF_lt_range n (by omega) h3
          ·
            by_cases h4 : n < 42500
            · exact CentBound8a.centF_lt_range n (by omega) h4
            ·
              exact CentBound8b.centF_lt_range n (by omega) (by omega)
  exact hasCentre_of_centredStar hc hcs hbnd

