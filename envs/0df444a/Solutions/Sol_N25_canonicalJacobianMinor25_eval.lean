-- Prove2me | solution 1 for N25.canonicalJacobianMinor25_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:53.066495+00:00
-- url     : https://prove2.me/submissions/e3203a7e-d6c6-412e-93a9-c926b7d970e1

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_N25_canonicalCubicGradient25_eval
import Theorems.Thm_N25_canonicalQuadricGradient25_eval

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

end MazurProof.RationalPointsN25QuotientSmoothF3

namespace N25

open scoped BigOperators

/-- The literal formal minor evaluates to the determinant of its two gradient columns. -/
theorem _root_.solution {K : Type*} [CommRing K]
    (v : Fin 4 → K) (j k : Fin 4) :
    MvPolynomial.eval v (canonicalJacobianMinor25 K j k) =
      canonicalQuadricGradient25 v j * canonicalCubicGradient25 v k -
        canonicalCubicGradient25 v j * canonicalQuadricGradient25 v k := by
  simp only [canonicalJacobianMinor25, map_sub, map_mul,
    canonicalQuadricGradient25_eval, canonicalCubicGradient25_eval]

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
