-- Prove2me | solution 1 for N25.Endgame.five_frobenius_fixed_places
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:24:30.341189+00:00
-- url     : https://prove2.me/submissions/4399091d-5ed9-4374-9b7f-5e1d191b4ca8

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
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_N25_Endgame_xHF2_degreeOnePlace_count25
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

namespace N25.Endgame

/-- The five degree-one places of the binary form are precisely the fixed
geometric places of Frobenius. -/
theorem _root_.solution (D₂ : RedDatum25 2) :
    (Function.fixedPoints (frobPlace25 D₂)).Finite ∧
      Nat.card (Function.fixedPoints (frobPlace25 D₂)) = 5 := by
  let : IsAlgClosed (κ D₂.A) := ValuationSubring.isAlgClosed_residueField D₂.A
  have hc := frobenius_fixedPlaces_card_eq_finiteField25
    2 (ZMod 2) (κ D₂.A) 1 (by decide) (by simp)
  simp only [Function.iterate_one] at hc
  have hcard : Nat.card (Function.fixedPoints (frobPlace25 D₂)) = 5 :=
    hc.trans xHF2_degreeOnePlace_count25
  let : Finite (Function.fixedPoints (frobPlace25 D₂)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  exact ⟨Set.toFinite _, hcard⟩

end N25.Endgame
