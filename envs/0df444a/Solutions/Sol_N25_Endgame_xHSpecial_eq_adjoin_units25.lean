-- Prove2me | solution 1 for N25.Endgame.xHSpecial_eq_adjoin_units25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:08.151449+00:00
-- url     : https://prove2.me/submissions/495ea75d-df79-47d7-9183-257e36cf29bf

import Mathlib
import Theorems.Thm_N25_Endgame_specialUnit_zero_finrank25
import Theorems.Thm_N25_Endgame_specialUnit_ratio_finrank25
import Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_specialUnit_zero_transcendental25
import Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_specialUnit_ratio_transcendental25
import Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_special_simple_finiteDimensional25
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_N25_Endgame_adjoin_pair_eq_top_of_coprime_finrank
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType

set_option autoImplicit false

noncomputable section

open AlgebraicCurve N25.Endgame

namespace N25.Endgame

open N25 SpecialUnitPoleDegrees

variable {p : ℕ} [Fact p.Prime] (hp : p = 2 ∨ p = 3) (R : RedDatum25 p)

include hp

/-- The complete reduced unit divisors have coprime pole degrees four and seven. -/
theorem _root_.solution :
    IntermediateField.adjoin (κ R.A)
      ({U25C (κ R.A) 0, U25C (κ R.A) 0 / U25C (κ R.A) 1} : Set (FSpecial R.A)) = ⊤ := by
  have hfour := specialUnit_zero_finrank25 hp R
  have hseven := specialUnit_ratio_finrank25 hp R
  let : FiniteDimensional
      (IntermediateField.adjoin (κ R.A) ({U25C (κ R.A) 0} : Set (FSpecial R.A)))
      (FSpecial R.A) := special_simple_finiteDimensional25 R _ (specialUnit_zero_transcendental25 hp R)
  let : FiniteDimensional
      (IntermediateField.adjoin (κ R.A)
        ({U25C (κ R.A) 0 / U25C (κ R.A) 1} : Set (FSpecial R.A)))
      (FSpecial R.A) := special_simple_finiteDimensional25 R _ (specialUnit_ratio_transcendental25 hp R)
  apply adjoin_pair_eq_top_of_coprime_finrank
  rw [hfour, hseven]
  norm_num

end N25.Endgame
