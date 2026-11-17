-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF3.residual_regular_bezout25Three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:32.306474+00:00
-- url     : https://prove2.me/submissions/9c6140c6-d559-4fd3-8de6-1f35f4daa7f7

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

/-- The residual and its two partial derivatives generate `z-1`.  Therefore
a critical point of the residual plane curve must lie on the exceptional
divisor `z=1`.  The displayed identity was discovered by Gröbner reduction;
Lean verifies the complete polynomial certificate independently. -/
theorem _root_.solution
    {K : Type*} [Field K] [CharP K 3] (y z : K) :
    (-y ^ 2 * z ^ 2 - y ^ 2 * z - y ^ 2 - y * z ^ 3 + y * z ^ 2 +
        y + z ^ 4 - z ^ 3 - z ^ 2 - 1) *
        canonicalResidualX25Three y z +
      (y ^ 3 * z + y ^ 3 + y ^ 2 * z ^ 2 + y ^ 2 * z - y * z ^ 3 +
        y * z ^ 2 + y * z - y + z ^ 3 - z ^ 2 - z - 1) *
        canonicalResidualYDerivative25Three y z +
      (y ^ 2 * z ^ 3 + y * z ^ 4 + y * z ^ 3 + y * z ^ 2 + y * z + y -
        z ^ 5 - z ^ 4 - z ^ 3 - z ^ 2 + z - 1) *
        canonicalResidualZDerivative25Three y z = z - 1 := by
  dsimp [canonicalResidualX25Three, canonicalResidualYDerivative25Three,
    canonicalResidualZDerivative25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  ring_nf
  simp [h3]

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
