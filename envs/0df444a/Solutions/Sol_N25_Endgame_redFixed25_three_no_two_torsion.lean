-- Prove2me | solution 1 for N25.Endgame.redFixed25_three_no_two_torsion
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:22:10.369231+00:00
-- url     : https://prove2.me/submissions/bccf12aa-065e-454e-ac3a-c3ea10eadf95

import Mathlib
import Theorems.Thm_N25_Endgame_ternaryLPolynomial25_zeta
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
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_N25_Endgame_xH25C_isCurveOver
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_N25_Endgame_ternaryLPolynomial25_eval_one
import Definitions.Def_N25_GenusFourNumerator
import Theorems.Thm_N25_Endgame_xH25C_constantsAreBase
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
import Theorems.Thm_N25_Endgame_xH25C_essFiniteType
import Theorems.Thm_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
import Theorems.Thm_AlgebraicCurve_exists_LPolynomial_of_finite
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Theorems.Thm_N25_Endgame_card_redFixed25_eq_pic0
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_Pic0_natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius
import Theorems.Thm_AlgebraicCurve_LPolynomial_eval_one_eq_natCard_pic0
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

/-! Absence of two-torsion in the Frobenius-fixed Picard group at three. -/
namespace N25.Endgame

/-- The full zeta identity and its value 71 exclude nonzero fixed two-torsion. -/
theorem _root_.solution
    (D₃ : RedDatum25 3) (z : ↥(RedFixed25 D₃))
    (h2z : (2 : ℕ) • z = 0) : z = 0 := by
  let : AlgebraicCurve.IsCurveOver (ZMod 3) F₃25 := xH25C_isCurveOver (ZMod 3)
  let : Algebra.EssFiniteType (ZMod 3) F₃25 := xH25C_essFiniteType (ZMod 3)
  have heval := AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0
    (ZMod 3) F₃25 (xH25C_constantsAreBase (ZMod 3)) ternaryLPolynomial25
    (by simpa [Nat.card_eq_fintype_card] using ternaryLPolynomial25_zeta)
  rw [ternaryLPolynomial25_eval_one] at heval
  have hpic : Nat.card (AlgebraicCurve.Pic0 (ZMod 3) F₃25) = 71 := by
    exact_mod_cast heval.symm
  have hcard : Nat.card ↥(RedFixed25 D₃) = 71 :=
    (card_redFixed25_eq_pic0 3 (by norm_num) D₃).trans hpic
  have hd₂ : addOrderOf z ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero h2z
  have hd₇₁ : addOrderOf z ∣ 71 := by
    simpa [hcard] using addOrderOf_dvd_natCard z
  have hd : addOrderOf z ∣ Nat.gcd 2 71 := Nat.dvd_gcd hd₂ hd₇₁
  norm_num at hd
  exact hd

end N25.Endgame
