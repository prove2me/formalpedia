-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF3.yChart_quadric25Three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:58.632996+00:00
-- url     : https://prove2.me/submissions/2dbcafac-ed66-41bc-b5fc-cd24b7bf42e4

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

/-- The quadric on the normalized `y`-chart factors as the displayed affine
equation. -/
theorem _root_.solution {K : Type*} [Field K] (z w : K) :
    canonicalQuadric25Three (⟨0, 1, z, w⟩ : Coordinates4 K) =
      1 + z + z * w := by
  unfold canonicalQuadric25Three
  ring

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
