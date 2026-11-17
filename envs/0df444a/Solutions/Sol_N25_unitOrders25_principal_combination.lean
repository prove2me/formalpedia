-- Prove2me | solution 1 for N25.unitOrders25_principal_combination
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:11.216575+00:00
-- url     : https://prove2.me/submissions/26b1f0e8-9d0f-4fd0-beb1-84e31d58e928

import Mathlib
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_U25C_ne_zero
import Theorems.Thm_N25_U25_orders_geometric
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
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

open AlgebraicCurve N25.Endgame

namespace N25

theorem _root_.solution (c : Fin 5 → ℤ) :
    Divisor.IsPrincipal (∑ r : Fin 5, c r •
      ∑ k : Fin 5, Finsupp.single (pG25 k) (unitOrders25 r k)) := by
  classical
  have hinj : Function.Injective pG25 := cuspChoice25_spec.2.2.1
  have hrow (r : Fin 5) :
      (∑ k : Fin 5, Finsupp.single (pG25 k) (unitOrders25 r k)) ∈
        Divisor.principal (K := Qbar) (F := FG) := by
    refine ⟨emb25 (U25 r), ?_, ?_⟩
    · intro h
      exact U25C_ne_zero ℚ r (emb25.injective (h.trans (map_zero emb25).symm))
    · intro P
      by_cases hP : ∃ j : Fin 5, P = pG25 j
      · obtain ⟨j, rfl⟩ := hP
        rw [(U25_orders_geometric r).1]
        simp [Finsupp.single_apply, hinj.eq_iff]
      · have hn (k : Fin 5) : pG25 k ≠ P := by
          intro h
          exact hP ⟨k, h.symm⟩
        rw [(U25_orders_geometric r).2 P (fun k h => hP ⟨k,h⟩)]
        simp [hn]
  change (∑ r : Fin 5, c r • ∑ k : Fin 5,
    Finsupp.single (pG25 k) (unitOrders25 r k)) ∈ Divisor.principal
  apply AddSubgroup.sum_mem
  intro r hr
  exact AddSubgroup.zsmul_mem _ (hrow r) (c r)

end N25
