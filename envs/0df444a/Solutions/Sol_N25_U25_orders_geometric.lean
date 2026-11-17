-- Prove2me | solution 1 for N25.U25_orders_geometric
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:08.211477+00:00
-- url     : https://prove2.me/submissions/d52488e7-cc55-4638-91b7-078ec0e2721a

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_U25_selected_geometric_order
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_N25_U25_geometric_ord_eq_zero_of_not_selected
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem

set_option autoImplicit false

open N25.Endgame

namespace N25

/-- The full geometric divisor of each original unpowered unit, in the signed cusp order. -/
theorem _root_.solution (i : Fin 5) :
    (∀ j : Fin 5, (pG25 j).ord (emb25 (U25 i)) = unitOrders25 i j) ∧
      ∀ P : GPlace, (∀ j : Fin 5, P ≠ pG25 j) → P.ord (emb25 (U25 i)) = 0 := by
  exact ⟨U25_selected_geometric_order i, U25_geometric_ord_eq_zero_of_not_selected i⟩

end N25
