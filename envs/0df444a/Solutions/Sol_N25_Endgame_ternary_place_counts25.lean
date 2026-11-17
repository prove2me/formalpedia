-- Prove2me | solution 1 for N25.Endgame.ternary_place_counts25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:22:09.703196+00:00
-- url     : https://prove2.me/submissions/8899a001-4190-4ef3-812e-496672d31717

import Definitions.Def_N25_FiniteBaseFunctionFields
import Definitions.Def_N25_CanonicalModularDictionaryGoodCharacteristic
import Definitions.Def_AlgebraicCurve_PlaceFieldEquiv
import Theorems.Thm_N25_Endgame_canonicalF9_degreeOnePlace_count25
import Theorems.Thm_N25_Endgame_canonicalF27_degreeOnePlace_count25
import Theorems.Thm_N25_Endgame_canonicalF81_degreeOnePlace_count25
import Theorems.Thm_N25_Endgame_canonicalF3_degreeOnePlace_count25
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

/-- The four ternary finite forms have the full canonical place counts. -/
theorem _root_.solution :
    Nat.card {P : AlgebraicCurve.Place (ZMod 3) F₃25 // P.deg = 1} = 5 ∧
    Nat.card {P : AlgebraicCurve.Place F9 (FBase F9) // P.deg = 1} = 5 ∧
    Nat.card {P : AlgebraicCurve.Place F27 (FBase F27) // P.deg = 1} = 20 ∧
    Nat.card {P : AlgebraicCurve.Place F81 (FBase F81) // P.deg = 1} = 89 := by
  rw [xHGood_degreeOnePlace_card_eq_canonical25 3 (Or.inr rfl) (ZMod 3),
    xHGood_degreeOnePlace_card_eq_canonical25 3 (Or.inr rfl) F9,
    xHGood_degreeOnePlace_card_eq_canonical25 3 (Or.inr rfl) F27,
    xHGood_degreeOnePlace_card_eq_canonical25 3 (Or.inr rfl) F81]
  exact ⟨canonicalF3_degreeOnePlace_count25, canonicalF9_degreeOnePlace_count25,
    canonicalF27_degreeOnePlace_count25, canonicalF81_degreeOnePlace_count25⟩

end N25.Endgame
