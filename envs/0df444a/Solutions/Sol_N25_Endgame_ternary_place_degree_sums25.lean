-- Prove2me | solution 1 for N25.Endgame.ternary_place_degree_sums25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:23:20.833198+00:00
-- url     : https://prove2.me/submissions/58ca3d82-092d-4793-b8b5-b6555a21483e

import Mathlib
import Theorems.Thm_N25_Endgame_ternary_place_counts25
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
import Theorems.Thm_N25_Endgame_frobenius_fixedPlaces_card_eq_finiteField25
import Definitions.Def_N25_Endgame
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
import Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThree_ternary_extension_cardinalities
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Theorems.Thm_N25_Endgame_frobenius_fixedPlaces_card_eq_degree_sum25
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

/-! The full zeta identity of the specified ternary modular function field. -/
noncomputable section

namespace N25.Endgame

open MazurProof.RationalPointsN25QuotientWeilThree

/-- The four weighted place counts on the literal prime-field form. -/
theorem _root_.solution :
    ∀ n : Fin 4,
      (∑ d ∈ Nat.divisors (n.val + 1), d *
        Nat.card {v : AlgebraicCurve.Place (ZMod 3) F₃25 | v.deg = d}) =
          (![5, 5, 20, 89] : Fin 4 → ℕ) n := by
  let K := AlgebraicClosure (ZMod 3)
  have h₁ := (frobenius_fixedPlaces_card_eq_degree_sum25 3 K 1 (by norm_num)).symm.trans
    ((frobenius_fixedPlaces_card_eq_finiteField25 3 (ZMod 3) K 1 (by norm_num)
      (by simp [Nat.card_eq_fintype_card])).trans ternary_place_counts25.1)
  have h₂ := (frobenius_fixedPlaces_card_eq_degree_sum25 3 K 2 (by norm_num)).symm.trans
    ((frobenius_fixedPlaces_card_eq_finiteField25 3 F9 K 2 (by norm_num)
      (by simpa [Nat.card_eq_fintype_card] using ternary_extension_cardinalities.2.1)).trans
        ternary_place_counts25.2.1)
  have h₃ := (frobenius_fixedPlaces_card_eq_degree_sum25 3 K 3 (by norm_num)).symm.trans
    ((frobenius_fixedPlaces_card_eq_finiteField25 3 F27 K 3 (by norm_num)
      (by simpa [Nat.card_eq_fintype_card] using ternary_extension_cardinalities.2.2.1)).trans
        ternary_place_counts25.2.2.1)
  have h₄ := (frobenius_fixedPlaces_card_eq_degree_sum25 3 K 4 (by norm_num)).symm.trans
    ((frobenius_fixedPlaces_card_eq_finiteField25 3 F81 K 4 (by norm_num)
      (by simpa [Nat.card_eq_fintype_card] using ternary_extension_cardinalities.2.2.2)).trans
        ternary_place_counts25.2.2.2)
  intro n
  fin_cases n
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

end N25.Endgame
