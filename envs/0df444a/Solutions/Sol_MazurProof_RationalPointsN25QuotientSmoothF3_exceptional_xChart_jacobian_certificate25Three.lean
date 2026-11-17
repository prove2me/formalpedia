-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF3.exceptional_xChart_jacobian_certificate25Three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:30.47676+00:00
-- url     : https://prove2.me/submissions/4a2ba7c8-8f89-4561-af16-f125e94e7674

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

/-! ## Exceptional divisor and boundary charts -/

/-- On the exceptional `x`-chart divisor `z=1`, the two curve equations and
the `yw` minor generate one.  This is the terminal two-variable certificate
for the only locus not covered by regular elimination. -/
theorem _root_.solution
    {K : Type*} [Field K] [CharP K 3] (y w : K) :
    (w ^ 2 - w) * (y ^ 2 + y - 1) +
      (-w * y + w + 1) * (y + w - w ^ 2) +
      (w ^ 2 + w * y + 1) * ((1 - y) * (1 + w)) = 1 := by
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
