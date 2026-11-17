-- Prove2me | solution 1 for N25.Endgame.canonical_point_card_eq_ternary25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:14:04.215212+00:00
-- url     : https://prove2.me/submissions/21278c2b-34b4-4aad-9434-aabb75f3ea71

import Definitions.Def_N25_CanonicalPointPlaces
import Theorems.Thm_N25_Endgame_isCanonicalNormalized25_iff_three
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Cardinality transport from full normalized canonical points to degree-one places. -/
namespace N25.Endgame

open N25

/-- The ternary field-semantic census uses exactly the full canonical point predicate. -/
theorem _root_.solution
    (K : Type*) [Field K] [CharP K 3] :
    Nat.card (CanonicalPoint25 K) =
      Nat.card {P : MazurProof.RationalPointsN25QuotientWeil.NormalizedProjective4 K //
        MazurProof.RationalPointsN25QuotientKummerThreeProjective.IsCanonicalNormalizedThree P} := by
  exact Nat.card_congr (Equiv.subtypeEquivRight (isCanonicalNormalized25_iff_three))

end N25.Endgame

namespace N25

end N25
