-- Prove2me | solution 1 for N25.unitOrders25_principal_seventyOne
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:11.812205+00:00
-- url     : https://prove2.me/submissions/2832275b-bf2c-4978-be75-91265ddbea3a

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_unitOrders25_annihilator_certificate
import Theorems.Thm_N25_unitOrders25_principal_combination
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

theorem _root_.solution (i j : Fin 5) :
    Divisor.IsPrincipal ((71 : ℤ) •
      (Finsupp.single (pG25 i) 1-Finsupp.single (pG25 j) 1)) := by
  classical
  let C : Fin 5 → Fin 5 → ℤ :=
    ![![0,0,0,0,0], ![12,1,17,26,0], ![1,6,31,14,0],
      ![17,31,30,25,0], ![26,14,25,9,0]]
  have hc := unitOrders25_annihilator_certificate
  change ∀ i j k : Fin 5, (∑ r : Fin 5, (C j r-C i r)*unitOrders25 r k) =
    71*((if k=i then 1 else 0)-(if k=j then 1 else 0)) at hc
  have hp := unitOrders25_principal_combination (fun r => C j r-C i r)
  have hinj : Function.Injective pG25 := cuspChoice25_spec.2.2.1
  have heq : (∑ r : Fin 5, (C j r-C i r) •
      ∑ k : Fin 5, Finsupp.single (pG25 k) (unitOrders25 r k)) =
      (71 : ℤ) • (Finsupp.single (pG25 i) 1-Finsupp.single (pG25 j) 1) := by
    ext P
    by_cases hP : ∃ k : Fin 5, P = pG25 k
    · obtain ⟨k, rfl⟩ := hP
      simpa [Finset.sum_apply, Finsupp.single_apply, hinj.eq_iff, eq_comm]
        using hc i j k
    · have hn (k : Fin 5) : pG25 k ≠ P := by
        intro h
        exact hP ⟨k,h.symm⟩
      simp [Finset.sum_apply, hn]
  rwa [heq] at hp

end N25
