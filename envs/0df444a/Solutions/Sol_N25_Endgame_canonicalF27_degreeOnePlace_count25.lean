-- Prove2me | solution 1 for N25.Endgame.canonicalF27_degreeOnePlace_count25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:15:16.971203+00:00
-- url     : https://prove2.me/submissions/e00c9df7-c11f-4553-b14f-f8e2852e9f4b

import Theorems.Thm_N25_Endgame_canonical_degreeOnePlace_card_eq_points25
import Theorems.Thm_N25_Endgame_canonical_point_card_eq_ternary25
import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitBinaryFieldSemantics
import Definitions.Def_N25_ExplicitSmallThreeSemantic
import Definitions.Def_N25_ExplicitF16Field
import Definitions.Def_N25_NormalizedPointPredicates
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmallThreeSemantic_f27_canonical_normalized_three_card
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Definitions.Def_N25_ExplicitKummerThreeF81
import Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25

/-! Finite-extension counts on the degree-one places of the full canonical curve. -/
namespace N25.Endgame

open N25

open MazurProof.RationalPointsN25QuotientBinaryFieldSemantics

open MazurProof.RationalPointsN25QuotientWeilThree

/-- The full canonical curve has 20 degree-one places over the field with 27 elements. -/
theorem _root_.solution :
    letI : IsDomain (CanonicalOpenChartRing25 F27) :=
      canonicalOpenChartRing_isDomain_good25 3 (Or.inr rfl) F27
    Nat.card {P : AlgebraicCurve.Place F27 (CanonicalFF25 F27) //
      P.deg = 1} = 20 := by
  rw [canonical_degreeOnePlace_card_eq_points25 3 (Or.inr rfl),
    canonical_point_card_eq_ternary25]
  exact MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f27_canonical_normalized_three_card

end N25.Endgame
