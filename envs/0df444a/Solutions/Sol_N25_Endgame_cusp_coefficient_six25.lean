-- Prove2me | solution 1 for N25.Endgame.cusp_coefficient_six25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:00.818606+00:00
-- url     : https://prove2.me/submissions/b26f79c9-b393-4ff9-8f78-ef66be8898ff

import Mathlib
import Definitions.Def_N25_PointDifference
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_Endgame_pG25_degree
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_unitOrders25_principal_combination
import Definitions.Def_N25_Units
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

open AlgebraicCurve N25

namespace N25.Endgame

theorem _root_.solution :
    pointDiff (pG25 0) (pG25 2) ((pG25_degree 0).trans (pG25_degree 2).symm) =
      (6 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) := by
  classical
  let D : Divisor.degZero (K := Qbar) (F := FG) :=
    ⟨Finsupp.single (pG25 0) 1-Finsupp.single (pG25 2) 1, by
      change Divisor.degree (Finsupp.single (pG25 0) 1-Finsupp.single (pG25 2) 1) = 0
      simp [pG25_degree]⟩
  let E : Divisor.degZero (K := Qbar) (F := FG) :=
    ⟨Finsupp.single (pG25 0) 1-Finsupp.single (pG25 1) 1, by
      change Divisor.degree (Finsupp.single (pG25 0) 1-Finsupp.single (pG25 1) 1) = 0
      simp [pG25_degree]⟩
  let c : Fin 5 → ℤ := ![-1,0,-1,-2,0]
  have hc : ∀ k : Fin 5, (∑ r : Fin 5, c r*unitOrders25 r k) =
      ((if k=0 then 1 else 0)-(if k=2 then 1 else 0))-
        6*((if k=0 then 1 else 0)-(if k=1 then 1 else 0)) := by decide
  have hp := unitOrders25_principal_combination c
  have hinj : Function.Injective pG25 := cuspChoice25_spec.2.2.1
  have heq : (∑ r : Fin 5, c r • ∑ k : Fin 5,
      Finsupp.single (pG25 k) (unitOrders25 r k)) =
      ((D-(6:ℤ) • E : Divisor.degZero (K := Qbar) (F := FG)) : Divisor Qbar FG) := by
    ext P
    by_cases hP : ∃ k : Fin 5, P = pG25 k
    · obtain ⟨k, rfl⟩ := hP
      simpa [D, E, Finset.sum_apply, Finsupp.single_apply, hinj.eq_iff, eq_comm]
        using hc k
    · have hn (k : Fin 5) : pG25 k ≠ P := by
        intro h
        exact hP ⟨k,h.symm⟩
      simp [D, E, Finset.sum_apply, hn]
  rw [heq] at hp
  let q : Divisor.degZero (K := Qbar) (F := FG) →+ Pic0 Qbar FG :=
    QuotientAddGroup.mk' _
  change q D = (6:ℤ) • q E
  apply sub_eq_zero.mp
  rw [← map_zsmul, ← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact hp

end N25.Endgame
