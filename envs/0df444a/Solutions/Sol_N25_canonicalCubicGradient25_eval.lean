-- Prove2me | solution 1 for N25.canonicalCubicGradient25_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:05.978053+00:00
-- url     : https://prove2.me/submissions/4916c231-50ed-4434-b605-a61a0d73fcc0

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

/-- Evaluating a formal cubic partial gives the displayed gradient entry. -/
theorem _root_.solution {K : Type*} [CommRing K]
    (v : Fin 4 → K) (j : Fin 4) :
    MvPolynomial.eval v
      (MvPolynomial.pderiv j (canonicalCubic
        (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3))) =
      canonicalCubicGradient25 v j := by
  fin_cases j <;> simp [canonicalCubic, canonicalCubicGradient25,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, Pi.single_apply] <;> ring

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
