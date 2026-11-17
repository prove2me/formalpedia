-- Prove2me | solution 1 for N25.Endgame.unitLaurentField25C_eq_modularField_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:01.576699+00:00
-- url     : https://prove2.me/submissions/f32e3287-eb45-46c2-9bd9-fbd84e7f94f4

import Mathlib
import Theorems.Thm_N25_unitLaurentField25C_le_modularField
import Theorems.Thm_N25_unitLaurentField25C_adjoin_coeffMap
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
import Theorems.Thm_N25_Endgame_unitLaurentField25C_relfinrank_pos

/-! Descent to the prime field and coefficient extension of generation by the modular units. -/
noncomputable section

namespace N25.Endgame

open N25 AlgebraicCurve

/-- Equality after coefficient extension descends because relative degree is preserved. -/
theorem _root_.solution
    (k K : Type*) [Field k] [PerfectField k] [Field K] [Algebra k K]
    (h : unitLaurentField25C K = ModularCurve.qExpFunctionFieldC K Γ25) :
    unitLaurentField25C k = ModularCurve.qExpFunctionFieldC k Γ25 := by
  have hdegree := ModularCurve.relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
    k K (unitLaurentField25C k) (ModularCurve.qExpFunctionFieldC k Γ25)
    (unitLaurentField25C_le_modularField k) (unitLaurentField25C_relfinrank_pos k)
  rw [unitLaurentField25C_adjoin_coeffMap,
    ← ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K,
    h] at hdegree
  have hone : IntermediateField.relfinrank (unitLaurentField25C k)
      (ModularCurve.qExpFunctionFieldC k Γ25) = 1 := by
    simpa using hdegree.symm
  exact le_antisymm (unitLaurentField25C_le_modularField k)
    (IntermediateField.relfinrank_eq_one_iff.mp hone)

end N25.Endgame
