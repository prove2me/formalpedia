-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF3.yChart_xy_minor_zero_branch25Three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:34.444934+00:00
-- url     : https://prove2.me/submissions/67c95b7e-6dfa-4d93-9a91-81cc4d846192

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientSmoothF3

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

/-- On the `y`-chart branch `w=0`, the quadric forces `z=-1`, where the
`xy` minor equals one. -/
theorem _root_.solution
    {K : Type*} [Field K] [CharP K 3] :
    (canonicalJacobianMinors25Three
      (⟨0, 1, -1, 0⟩ : Coordinates4 K)).xy = 1 := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  linear_combination -h3

end MazurProof.RationalPointsN25QuotientSmoothF3

namespace N25

open scoped BigOperators

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

end N25

namespace N25

end N25
