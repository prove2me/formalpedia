-- Prove2me | solution 1 for N25.Endgame.specialUnit_zero_finrank25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:12.003025+00:00
-- url     : https://prove2.me/submissions/2c54e79c-f1bf-4db2-be14-b46b0f9834a2

import Mathlib
import Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_finrank_eq_sum_poles
import Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_specialUnit_zero_transcendental25
import Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_special_simple_finiteDimensional25
import Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_special_zero_LSpace_finiteDimensional25
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_Endgame_xH25C_isCurveOver
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_N25_Endgame_U25_orders_special_good
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField

set_option autoImplicit false

noncomputable section

open AlgebraicCurve N25.Endgame

namespace N25.Endgame

open N25 SpecialUnitPoleDegrees

variable {p : ℕ} [Fact p.Prime] (hp : p = 2 ∨ p = 3) (R : RedDatum25 p)

include hp

/-- The complete divisor of the first reduced unit gives exact pole degree four. -/
theorem _root_.solution :
    Module.finrank
      (IntermediateField.adjoin (κ R.A) ({U25C (κ R.A) 0} : Set (FSpecial R.A)))
      (FSpecial R.A) = 4 := by
  let : IsAlgClosed (κ R.A) := ValuationSubring.isAlgClosed_residueField R.A
  let : IsCurveOver (κ R.A) (FSpecial R.A) := xH25C_isCurveOver (κ R.A)
  let : FiniteDimensional (κ R.A) (LSpace (0 : Divisor (κ R.A) (FSpecial R.A))) :=
    special_zero_LSpace_finiteDimensional25 R
  have ht := specialUnit_zero_transcendental25 hp R
  let : FiniteDimensional
      (IntermediateField.adjoin (κ R.A) ({U25C (κ R.A) 0} : Set (FSpecial R.A)))
      (FSpecial R.A) := special_simple_finiteDimensional25 R _ ht
  have h := finrank_eq_sum_poles hp R (U25C (κ R.A) 0) ht (unitOrders25 0)
    (U25_orders_special_good p hp R 0).1 (U25_orders_special_good p hp R 0).2
  have hsum : (∑ i : Fin 5, max 0 (-unitOrders25 0 i)) = (4 : ℤ) := by
    norm_num [Fin.sum_univ_succ, unitOrders25]
  rw [hsum] at h
  exact Int.ofNat_inj.mp h

end N25.Endgame
