-- Prove2me | solution 1 for N25.canonicalCubicGradient25_euler
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:05.419476+00:00
-- url     : https://prove2.me/submissions/2dc32c1d-ec13-4fa0-9f37-d6582a09df50

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

end MazurProof.RationalPointsN25QuotientSmoothF3

namespace N25

open scoped BigOperators

/-- Euler's identity for the degree-three canonical equation. -/
theorem _root_.solution {K : Type*} [CommRing K] (v : Fin 4 → K) :
    ∑ j : Fin 4, v j * canonicalCubicGradient25 v j =
      3 * canonicalCubic (v 0) (v 1) (v 2) (v 3) := by
  simp [Fin.sum_univ_succ, canonicalCubicGradient25, canonicalCubic]
  ring

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
