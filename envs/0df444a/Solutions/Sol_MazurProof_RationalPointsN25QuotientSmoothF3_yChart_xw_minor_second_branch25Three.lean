-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF3.yChart_xw_minor_second_branch25Three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:59.270199+00:00
-- url     : https://prove2.me/submissions/8cea6896-0237-44a4-80b7-8d3df13a153c

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

/-- On the second `y`-chart branch `w=1+z`, the `xw` minor is `z²-z`.
Together with the quadric relation `z²-z+1=0`, it cannot vanish. -/
theorem _root_.solution
    {K : Type*} [Field K] [CharP K 3] (z : K) :
    (canonicalJacobianMinors25Three
      (⟨0, 1, z, 1 + z⟩ : Coordinates4 K)).xw = z ^ 2 - z := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  linear_combination (-2 * z ^ 2 - z ^ 3) * h3

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
