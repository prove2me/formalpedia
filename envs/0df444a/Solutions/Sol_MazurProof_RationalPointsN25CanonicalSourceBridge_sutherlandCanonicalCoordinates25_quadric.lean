-- Prove2me | solution 1 for MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalCoordinates25_quadric
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:02.219377+00:00
-- url     : https://prove2.me/submissions/beb20b41-1aaf-45dc-8f5f-3cdf9398a4bb

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalPoints
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Definitions.Def_RationalPointsN25QuotientAction
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_CanonicalZCoordinate` and their helpers. -/

namespace MazurProof.RationalPointsN25CanonicalSourceBridge

open RationalPointsN25CanonicalPoints

open RationalPointsN25QuotientAction

open RationalPointsN25SutherlandBridge

open TateOrder25Factor

/-- Pulling back the target canonical quadric gives Sutherland's source
equation times the displayed degree-six cofactor. -/
theorem _root_.solution (x y : ℚ) :
    canonicalQuadric25
        (sutherlandCanonicalCoordinates25 x y).x
        (sutherlandCanonicalCoordinates25 x y).y
        (sutherlandCanonicalCoordinates25 x y).z
        (sutherlandCanonicalCoordinates25 x y).w =
      sutherlandCanonicalQuadricCofactor25 x y *
        sutherlandX1Plane25 x y := by
  simp only [sutherlandCanonicalCoordinates25, sutherlandCanonicalX25,
    sutherlandCanonicalXCore25, sutherlandCanonicalY25,
    sutherlandCanonicalZ25, sutherlandCanonicalW25,
    sutherlandCanonicalWCore25, sutherlandCanonicalQuadricCofactor25,
    sutherlandX1Plane25, canonicalQuadric25]
  ring

end MazurProof.RationalPointsN25CanonicalSourceBridge
