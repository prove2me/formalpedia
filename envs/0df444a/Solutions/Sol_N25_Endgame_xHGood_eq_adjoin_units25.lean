-- Prove2me | solution 1 for N25.Endgame.xHGood_eq_adjoin_units25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:00:42.898642+00:00
-- url     : https://prove2.me/submissions/39ca7579-23ea-49f4-9575-c606e1bdb918

import Mathlib
import Theorems.Thm_N25_unitLaurentField25C_eq_modularField_iff
import Theorems.Thm_N25_unitLaurentField25C_eq_modularField_of_coefficients
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
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
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
import Theorems.Thm_N25_Endgame_xHGoodPrime_eq_adjoin_units25

/-! Descent to the prime field and coefficient extension of generation by the modular units. -/
noncomputable section

namespace N25.Endgame

open N25 AlgebraicCurve

/-- The specified two modular units generate the good-characteristic modular function field. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    IntermediateField.adjoin K
      ({U25C K 0, U25C K 0 / U25C K 1} : Set (FBase K)) = ⊤ := by
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  have hprime : unitLaurentField25C (ZMod p) =
      ModularCurve.qExpFunctionFieldC (ZMod p) Γ25 :=
    (unitLaurentField25C_eq_modularField_iff (ZMod p)).mpr
      (xHGoodPrime_eq_adjoin_units25 p hp)
  exact (unitLaurentField25C_eq_modularField_iff K).mp
    (unitLaurentField25C_eq_modularField_of_coefficients (ZMod p) K hprime)

end N25.Endgame
