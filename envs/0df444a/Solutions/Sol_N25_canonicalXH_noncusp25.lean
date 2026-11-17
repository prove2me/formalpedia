-- Prove2me | solution 1 for N25.canonicalXH_noncusp25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:19:48.3045+00:00
-- url     : https://prove2.me/submissions/ed0c663a-2343-4a67-a413-2ddd89c2b1c8

import Mathlib
import Theorems.Thm_N25_canonicalXHAlgEquiv25_coordinates
import Theorems.Thm_N25_canonicalXHPlaceEquiv25_degree
import Theorems.Thm_N25_canonicalXHPlaceEquiv25_order
import Definitions.Def_N25_CanonicalModularDictionary
import Theorems.Thm_N25_canonicalNoncuspPlace25_unit_orders
import Definitions.Def_N25_CanonicalFunctionCoordinates
import Definitions.Def_N25_CanonicalNoncuspPlace
import Theorems.Thm_N25_canonicalNoncuspPlace25_degree
import Definitions.Def_N25_UnitPlanePointPlace
import Theorems.Thm_N25_cuspArithmeticCensus
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
import Theorems.Thm_ModularCurve_coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_N25_U25_orders_rational
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem

/-! Rational noncuspidal canonical points remain noncuspidal on the modular curve. -/
namespace N25

open MazurProof.RationalPointsN25CanonicalPoints

open N25.Endgame

/-- A degree-one modular cusp has nonzero order on the first specified unit. -/
private theorem rational_cusp_first_unit_order_ne_zero
    (P : QPlace) (hP : P.deg = 1) (hcusp : ModularCurve.IsCusp j25 P) :
    P.ord (U25 0) ≠ 0 := by
  obtain ⟨P4, P5, hd4, hd5, _, _, hclass, _⟩ := N25.cuspArithmeticCensus
  have hs : ∃ i : Fin 5, P = pQ25 i := by
    rcases (hclass P).mp hcusp with hs | h4 | h5
    · exact hs
    · subst P
      omega
    · subst P
      omega
  obtain ⟨i, rfl⟩ := hs
  rw [(U25_orders_rational 0).1 i]
  fin_cases i <;> norm_num [unitOrders25]

/-- Zero unit order at a noncuspidal canonical point excludes every rational modular cusp. -/
theorem _root_.solution
    (x y z w : ℚ)
    (hnz : NonzeroQuadruple x y z w)
    (hq : canonicalQuadric x y z w = 0)
    (hc : canonicalCubic x y z w = 0)
    (hnc : ¬ IsCanonicalCusp25 x y z w) :
    ¬ ModularCurve.IsCusp N25.Endgame.j25
      (canonicalXHPlaceEquiv25
        (canonicalNoncuspPlace25 x y z w hnz hq hc hnc)) := by
  intro hcusp
  let P := canonicalNoncuspPlace25 x y z w hnz hq hc hnc
  have hdegree : (canonicalXHPlaceEquiv25 P).deg = 1 := by
    rw [canonicalXHPlaceEquiv25_degree]
    exact canonicalNoncuspPlace25_degree x y z w hnz hq hc hnc
  have hzero : (canonicalXHPlaceEquiv25 P).ord (U25 0) = 0 := by
    rw [← canonicalXHAlgEquiv25_coordinates.1, canonicalXHPlaceEquiv25_order]
    exact (canonicalNoncuspPlace25_unit_orders x y z w hnz hq hc hnc).1
  exact rational_cusp_first_unit_order_ne_zero _ hdegree hcusp hzero

end N25
