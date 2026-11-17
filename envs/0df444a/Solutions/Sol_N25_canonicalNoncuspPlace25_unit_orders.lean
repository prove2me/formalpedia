-- Prove2me | solution 1 for N25.canonicalNoncuspPlace25_unit_orders
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:28.02194+00:00
-- url     : https://prove2.me/submissions/911a5a79-3740-4007-bb93-36d836162474

import Definitions.Def_N25_CanonicalFunctionCoordinates
import Definitions.Def_N25_CanonicalNoncuspPlace
import Theorems.Thm_N25_canonicalPointPlaceOfUnitPlane25_unit_orders

/-! Noncuspidal canonical points make both distinguished functions local units. -/
noncomputable section

namespace N25

open MazurProof.RationalPointsN25CanonicalPoints

/-- A rational canonical point outside the five cusp classes has unit orders
for the two distinguished canonical functions. -/
theorem _root_.solution
    (x y z w : ℚ)
    (hnz : NonzeroQuadruple x y z w)
    (hq : canonicalQuadric x y z w = 0)
    (hc : canonicalCubic x y z w = 0)
    (hnc : ¬ IsCanonicalCusp25 x y z w) :
    (canonicalNoncuspPlace25 x y z w hnz hq hc hnc).ord
        canonicalFunctionU25 = 0 ∧
      (canonicalNoncuspPlace25 x y z w hnz hq hc hnc).ord
        canonicalFunctionV25 = 0 := by
  have h := canonical_noncuspidal_denominators hnz hq hc hnc
  exact canonicalPointPlaceOfUnitPlane25_unit_orders
    (x / canonicalDenominator y z w) (x ^ 2 / (z * canonicalDenominator y z w))
    (canonical_maps_to_plane x y z w h.1 h.2.2.1 h.2.1 hq hc)
    (div_ne_zero h.1 h.2.2.1)
    (div_ne_zero (pow_ne_zero 2 h.1) (mul_ne_zero h.2.1 h.2.2.1))

end N25
