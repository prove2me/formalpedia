-- Prove2me | solution 1 for N25.Endgame.frobenius_fixedPlaces_card_eq_degree_sum25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:22:07.767166+00:00
-- url     : https://prove2.me/submissions/0c2ca7fd-ddb6-4da7-843e-f525a2db8f15

import Mathlib
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
import Theorems.Thm_N25_Endgame_xH25C_finitelyGenerated
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_N25_Endgame_FBaseCoeffMap25_generates
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_N25_Endgame_FBaseCoeffMap25_frobenius_prime
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

/-! The full zeta identity of the specified ternary modular function field. -/
noncomputable section

namespace N25.Endgame

open MazurProof.RationalPointsN25QuotientWeilThree

/-- The weighted closed-place count equals the fixed points of prime Frobenius iterated n times. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (hn : 0 < n) :
    Nat.card (Function.fixedPoints ((ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n])) =
      ∑ d ∈ Nat.divisors n, d *
        Nat.card {v : AlgebraicCurve.Place (ZMod p) (FBase (ZMod p)) | v.deg = d} := by
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (FBase (ZMod p)) (FBase K) :=
    (FBaseCoeffMap25 (ZMod p) K).toAlgebra
  let : AlgebraicCurve.IsCurveOver (ZMod p) (FBase (ZMod p)) :=
    xH25C_isCurveOver (ZMod p)
  let : AlgebraicCurve.IsCurveOver K (FBase K) := xH25C_isCurveOver K
  have h := AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
    (ZMod p) K (FBase (ZMod p)) (FBase K)
    (xH25C_finitelyGenerated (ZMod p)) (FBaseCoeffMap25_generates (ZMod p) K)
    (ModularCurve.qExpFrobeniusModL K Γ25 p)
    (ModularCurve.qExpFrobeniusModL_isIntegral K Γ25 p)
    (fun x => by
      change ModularCurve.qExpFrobeniusModL K Γ25 p (FBaseCoeffMap25 (ZMod p) K x) =
        FBaseCoeffMap25 (ZMod p) K (x ^ Nat.card (ZMod p))
      rw [Nat.card_eq_fintype_card, ZMod.card]
      exact FBaseCoeffMap25_frobenius_prime p K x) n hn
  exact h.2

end N25.Endgame
