-- Prove2me | solution 1 for N25.Endgame.cusp_difference_killed25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:09.533199+00:00
-- url     : https://prove2.me/submissions/9485e0cc-43cb-4e98-97b7-61f913f27340

import Mathlib
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_unitOrders25_principal_seventyOne
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
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
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

open AlgebraicCurve

namespace N25.Endgame

theorem _root_.solution (i j : Fin 5) :
    (71 : ℕ) • pointDiff (pG25 i) (pG25 j)
      ((pG25_degree i).trans (pG25_degree j).symm) = 0 := by
  let D : Divisor.degZero (K := Qbar) (F := FG) :=
    ⟨Finsupp.single (pG25 i) 1-Finsupp.single (pG25 j) 1, by
      change Divisor.degree (Finsupp.single (pG25 i) 1-Finsupp.single (pG25 j) 1) = 0
      simp [pG25_degree]⟩
  change (71 : ℕ) • Pic0.mk D = 0
  have hz : (71 : ℤ) • Pic0.mk D = 0 := by
    have hm : (71 : ℤ) • Pic0.mk D = Pic0.mk ((71 : ℤ) • D) := by
      exact (QuotientAddGroup.mk_zsmul
        ((Divisor.principal (K := Qbar) (F := FG)).addSubgroupOf
          (Divisor.degZero (K := Qbar) (F := FG))) D (71 : ℤ)).symm
    rw [hm]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    change Divisor.IsPrincipal ((71 : ℤ) •
      (Finsupp.single (pG25 i) 1-Finsupp.single (pG25 j) 1))
    exact N25.unitOrders25_principal_seventyOne i j
  have hcast : ((71 : ℕ) : ℤ) • Pic0.mk D = (71 : ℕ) • Pic0.mk D := natCast_zsmul _ _
  exact hcast.symm.trans hz

end N25.Endgame
