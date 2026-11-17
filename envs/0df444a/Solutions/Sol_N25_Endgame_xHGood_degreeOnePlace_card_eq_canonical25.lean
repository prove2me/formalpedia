-- Prove2me | solution 1 for N25.Endgame.xHGood_degreeOnePlace_card_eq_canonical25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:22:09.021519+00:00
-- url     : https://prove2.me/submissions/803439c1-2e4d-451e-9c6d-de58110fb846

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
import Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25

/-! Transport of the full canonical place census to the specified modular finite forms. -/
noncomputable section

namespace N25.Endgame

open N25

open MazurProof.RationalPointsN25QuotientWeilThree

/-- The coordinate-pinned dictionary preserves degree-one place cardinalities. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    letI : IsDomain (CanonicalOpenChartRing25 K) :=
      canonicalOpenChartRing_isDomain_good25 p hp K
    Nat.card {P : AlgebraicCurve.Place K (FBase K) // P.deg = 1} =
      Nat.card {P : AlgebraicCurve.Place K (CanonicalFF25 K) // P.deg = 1} := by
  let : IsDomain (CanonicalOpenChartRing25 K) :=
    canonicalOpenChartRing_isDomain_good25 p hp K
  exact Nat.card_congr
    (AlgebraicCurve.Place.degreeOneAlgEquiv (canonicalXHGoodCharAlgEquiv25 p hp K)).symm

end N25.Endgame
