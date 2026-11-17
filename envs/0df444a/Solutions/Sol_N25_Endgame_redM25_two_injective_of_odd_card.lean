-- Prove2me | solution 1 for N25.Endgame.redM25_two_injective_of_odd_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:20:57.639324+00:00
-- url     : https://prove2.me/submissions/269bf4a6-c669-4abc-ae82-2c10080f21d0

import Mathlib
import Definitions.Def_N25_ReductionMap
import Theorems.Thm_N25_Endgame_coe_redM25
import Theorems.Thm_N25_Endgame_eq_zero_of_red25_eq_zero
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Definitions.Def_N25_FiniteBaseFunctionFields
import Definitions.Def_N25_CanonicalModularDictionaryGoodCharacteristic
import Definitions.Def_AlgebraicCurve_PlaceFieldEquiv
import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitBinaryFieldSemantics
import Definitions.Def_N25_ExplicitSmallThreeSemantic
import Definitions.Def_N25_ExplicitF16Field
import Definitions.Def_N25_NormalizedPointPredicates
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Definitions.Def_N25_GenusFourNumerator
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
import Theorems.Thm_AlgebraicCurve_exists_LPolynomial_of_finite
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_Pic0_natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius
import Theorems.Thm_AlgebraicCurve_LPolynomial_eval_one_eq_natCard_pic0

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

/-- Odd rational cardinality makes reduction at two injective. -/
theorem _root_.solution (hfin : Finite ↥N25.M)
    (hodd : Odd (Nat.card ↥N25.M)) (D₂ : RedDatum25 2) :
    Function.Injective (redM25 (by norm_num) D₂) := by
  let : Finite ↥N25.M := hfin
  apply (injective_iff_map_eq_zero (redM25 (by norm_num) D₂)).mpr
  intro x hx
  apply Subtype.ext
  apply eq_zero_of_red25_eq_zero (by norm_num) D₂ (Nat.card ↥N25.M)
  · exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  · exact congrArg (fun z : ↥N25.M => (z : N25.J)) ((addOrderOf_dvd_iff_nsmul_eq_zero).mp (addOrderOf_dvd_natCard x))
  · exact (coe_redM25 (by norm_num) D₂ x).symm.trans
      (congrArg (fun z : ↥(RedFixed25 D₂) => (z : SpecialPic D₂.A)) hx)

end N25.Endgame
