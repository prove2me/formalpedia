-- Prove2me | solution 1 for N25.Endgame.isCanonicalNormalized25_iff_three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:49.512427+00:00
-- url     : https://prove2.me/submissions/eba341ed-7f8c-4fc2-b26a-c254bafe31ec

import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! The normalized point carrier agrees with both finite-characteristic predicates. -/

namespace N25.Endgame

open MazurProof.RationalPointsN25QuotientWeil

theorem _root_.solution
    {K : Type*} [Field K] [CharP K 3]
    (P : NormalizedProjective4 K) :
    IsCanonicalNormalized25 P ↔
      MazurProof.RationalPointsN25QuotientKummerThreeProjective.IsCanonicalNormalizedThree P := by
  cases P <;> rfl

end N25.Endgame
