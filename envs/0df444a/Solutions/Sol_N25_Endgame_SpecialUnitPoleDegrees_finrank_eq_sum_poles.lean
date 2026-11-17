-- Prove2me | solution 1 for N25.Endgame.SpecialUnitPoleDegrees.finrank_eq_sum_poles
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:12.708966+00:00
-- url     : https://prove2.me/submissions/23140ec6-8624-4796-931f-6012ea3de1c8

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_Endgame_cusp_reductions_injective_good
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
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
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_N25_Endgame_redPlace25_degree
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
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

set_option autoImplicit false

noncomputable section

open AlgebraicCurve N25.Endgame

namespace N25.Endgame

open N25

variable {p : ℕ} [Fact p.Prime] (hp : p = 2 ∨ p = 3) (R : RedDatum25 p)

include hp

namespace SpecialUnitPoleDegrees

/-- A complete list of the orders computes the degree over the simple subfield. -/
theorem _root_.solution
    [IsCurveOver (κ R.A) (FSpecial R.A)] [FiniteDimensional (κ R.A) (LSpace (0 : Divisor (κ R.A) (FSpecial R.A)))]
    (f : (FSpecial R.A)) (hf : Transcendental (κ R.A) f)
    [FiniteDimensional (IntermediateField.adjoin (κ R.A) ({f} : Set (FSpecial R.A))) (FSpecial R.A)]
    (a : Fin 5 → ℤ) (ha : ∀ i, (redPlace25 R (pG25 i)).ord f = a i)
    (hs : ∀ P : (SpecialPlace R.A), (∀ i, P ≠ redPlace25 R (pG25 i)) → P.ord f = 0) :
    (Module.finrank (IntermediateField.adjoin (κ R.A) ({f} : Set (FSpecial R.A))) (FSpecial R.A) : ℤ) =
      ∑ i : Fin 5, max 0 (-a i) := by
  classical
  let D : Divisor (κ R.A) (FSpecial R.A) := ∑ i : Fin 5, Finsupp.single (redPlace25 R (pG25 i)) (max 0 (-a i))
  have hinj : Function.Injective (fun i => redPlace25 R (pG25 i)) :=
    cusp_reductions_injective_good p hp R
  have hD (P : (SpecialPlace R.A)) : D P = max 0 (-P.ord f) := by
    by_cases hP : ∃ i : Fin 5, P = redPlace25 R (pG25 i)
    · obtain ⟨i, rfl⟩ := hP
      simp [D, Finset.sum_apply, Finsupp.single_apply, hinj.eq_iff, eq_comm, ha]
    · have hn (i : Fin 5) : redPlace25 R (pG25 i) ≠ P := by
        intro h
        exact hP ⟨i, h.symm⟩
      have hz : P.ord f = 0 := hs P (fun i h => hP ⟨i, h⟩)
      simp [D, Finset.sum_apply, hn, hz]
  calc
    _ = Divisor.degree D :=
      (Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord f hf D hD).symm
    _ = _ := by simp [D, map_sum, Divisor.degree_single, redPlace25_degree, pG25_degree]

end SpecialUnitPoleDegrees

end N25.Endgame
