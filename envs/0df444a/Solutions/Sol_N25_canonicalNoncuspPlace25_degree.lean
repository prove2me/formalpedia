-- Prove2me | solution 1 for N25.canonicalNoncuspPlace25_degree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:46.486479+00:00
-- url     : https://prove2.me/submissions/2c29b4b2-5ecc-4f36-9b6b-4e604f693997

import Definitions.Def_N25_CanonicalNoncuspPlace
import Theorems.Thm_N25_canonicalPointPlaceOfUnitPlane25_degree
import Definitions.Def_N25_UnitPlanePointPlace

namespace N25

/-- Every rational noncuspidal canonical point gives a degree-one place. -/
theorem _root_.solution (x y z w : ℚ)
    (hnz : MazurProof.RationalPointsN25CanonicalPoints.NonzeroQuadruple x y z w)
    (hq : canonicalQuadric x y z w = 0) (hc : canonicalCubic x y z w = 0)
    (hnc : ¬ MazurProof.RationalPointsN25CanonicalPoints.IsCanonicalCusp25 x y z w) :
    (canonicalNoncuspPlace25 x y z w hnz hq hc hnc).deg = 1 :=
  canonicalPointPlaceOfUnitPlane25_degree _ _ _ _

end N25
