-- Prove2me | solution 1 for N25.Endgame.xHF2_degreeOnePlace_count25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:24:29.727521+00:00
-- url     : https://prove2.me/submissions/fbbc024f-5680-4b5f-ad93-75820aebd457

import Definitions.Def_N25_FiniteBaseFunctionFields
import Definitions.Def_N25_CanonicalModularDictionaryGoodCharacteristic
import Definitions.Def_AlgebraicCurve_PlaceFieldEquiv
import Theorems.Thm_N25_Endgame_canonicalF2_degreeOnePlace_count25
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
import Theorems.Thm_N25_Endgame_xHGood_degreeOnePlace_card_eq_canonical25

/-! Transport of the full canonical place census to the specified modular finite forms. -/
noncomputable section

namespace N25.Endgame

open N25

open MazurProof.RationalPointsN25QuotientWeilThree

/-- The binary modular finite form has exactly five degree-one places. -/
theorem _root_.solution :
    Nat.card {P : AlgebraicCurve.Place (ZMod 2) F₂25 // P.deg = 1} = 5 := by
  rw [xHGood_degreeOnePlace_card_eq_canonical25 2 (Or.inl rfl)]
  exact canonicalF2_degreeOnePlace_count25

end N25.Endgame
