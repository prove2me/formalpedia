-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.AllDensCentred_R0
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:36:43.48156+00:00
-- url     : https://prove2.me/submissions/58386034-fa17-41b6-89fd-80ba0edc2836

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound1a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound1b
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentBound2
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

theorem solution : ∀ n < 15000, HasCentre (densSupG n) := by
  intro n hn
  have hbnd : ∀ i, (densSupG n).testBit i = true → i < 1771 := by
    intro i hi
    have hlt : densSupG n < 2 ^ 1771 := by
      by_cases h0 : n < 5000
      · exact CentBound0.densSupG_lt_range n (by omega) h0
      ·
        by_cases h1 : n < 7500
        · exact CentBound1a.densSupG_lt_range n (by omega) h1
        ·
          by_cases h2 : n < 10000
          · exact CentBound1b.densSupG_lt_range n (by omega) h2
          ·
            exact CentBound2.densSupG_lt_range n (by omega) (by omega)
    by_contra hge
    have : (densSupG n).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) (Nat.le_of_not_gt hge)))
    exact Bool.false_ne_true (this ▸ hi)
  have hcs : centredStar (densSupG n) (centF n) = true := by
    by_cases h0 : n < 5000
    · exact CentBound0.centredStar_range n (by omega) h0
    ·
      by_cases h1 : n < 7500
      · exact CentBound1a.centredStar_range n (by omega) h1
      ·
        by_cases h2 : n < 10000
        · exact CentBound1b.centredStar_range n (by omega) h2
        ·
          exact CentBound2.centredStar_range n (by omega) (by omega)
  have hc : centF n < 23 := by
    by_cases h0 : n < 5000
    · exact CentBound0.centF_lt_range n (by omega) h0
    ·
      by_cases h1 : n < 7500
      · exact CentBound1a.centF_lt_range n (by omega) h1
      ·
        by_cases h2 : n < 10000
        · exact CentBound1b.centF_lt_range n (by omega) h2
        ·
          exact CentBound2.centF_lt_range n (by omega) (by omega)
  exact hasCentre_of_centredStar hc hcs hbnd

