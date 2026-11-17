-- Prove2me | solution 1 for N25.Endgame.canonicalF81_degreeOnePlace_count25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:14:05.19793+00:00
-- url     : https://prove2.me/submissions/26ffc3d4-b8dc-475c-bd68-b4e534175f9e

import Theorems.Thm_N25_Endgame_canonical_degreeOnePlace_card_eq_points25
import Theorems.Thm_N25_Endgame_canonical_point_card_eq_ternary25
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
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeProjective_f81_canonical_normalized_three_card
import Definitions.Def_N25_ExplicitKummerThreeF81
import Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25

/-! Finite-extension counts on the degree-one places of the full canonical curve. -/
namespace N25.Endgame

open N25

open MazurProof.RationalPointsN25QuotientBinaryFieldSemantics

open MazurProof.RationalPointsN25QuotientWeilThree

/-- The full canonical curve has 89 degree-one places over the field with 81 elements. -/
theorem _root_.solution :
    letI : IsDomain (CanonicalOpenChartRing25 F81) :=
      canonicalOpenChartRing_isDomain_good25 3 (Or.inr rfl) F81
    Nat.card {P : AlgebraicCurve.Place F81 (CanonicalFF25 F81) //
      P.deg = 1} = 89 := by
  rw [canonical_degreeOnePlace_card_eq_points25 3 (Or.inr rfl),
    canonical_point_card_eq_ternary25]
  exact MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_canonical_normalized_three_card

end N25.Endgame
