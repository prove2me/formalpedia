-- Prove2me | solution 1 for N25.Endgame.rational_eq_zero_of_two_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:22:11.037906+00:00
-- url     : https://prove2.me/submissions/5e8b08e4-16a2-4baf-bdbf-2d6d9a06ceea

import Mathlib
import Definitions.Def_N25_ReductionMap
import Theorems.Thm_N25_Endgame_coe_redM25
import Theorems.Thm_N25_Endgame_eq_zero_of_red25_eq_zero
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_N25_Endgame_redFixed25_three_no_two_torsion
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

/-- Prime-to-three specialization and absence of fixed two-torsion exclude rational two-torsion. -/
theorem _root_.solution (D₃ : RedDatum25 3)
    (x : ↥N25.M) (hx : (2 : ℕ) • x = 0) : x = 0 := by
  have hr : (2 : ℕ) • redM25 (by norm_num) D₃ x = 0 := by
    rw [← map_nsmul, hx, map_zero]
  have hz := redFixed25_three_no_two_torsion D₃ _ hr
  apply Subtype.ext
  apply eq_zero_of_red25_eq_zero (by norm_num) D₃ 2 (by norm_num)
  · exact congrArg (fun z : ↥N25.M => (z : N25.J)) hx
  · exact (coe_redM25 (by norm_num) D₃ x).symm.trans
      (congrArg (fun z : ↥(RedFixed25 D₃) => (z : SpecialPic D₃.A)) hz)

end N25.Endgame
