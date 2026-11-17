-- Prove2me | solution 1 for MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_onCanonical
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:01.270393+00:00
-- url     : https://prove2.me/submissions/358f0331-837f-4359-88a1-c80436c071a9

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalPoints
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Definitions.Def_RationalPointsN25QuotientAction
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandCanonicalCoordinates25_quadric
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherland_on_plane

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandToCanonical` and their helpers. -/

namespace MazurProof.RationalPointsN25CanonicalSourceBridge

open RationalPointsN25CanonicalPoints

open RationalPointsN25QuotientAction

open RationalPointsN25SutherlandBridge

open TateOrder25Factor

/-- Pulling back the target canonical cubic gives Sutherland's source
equation times the displayed degree-fifteen cofactor. -/
theorem sutherlandCanonicalCoordinates25_cubic (x y : ℚ) :
    canonicalCubic25
        (sutherlandCanonicalCoordinates25 x y).x
        (sutherlandCanonicalCoordinates25 x y).y
        (sutherlandCanonicalCoordinates25 x y).z
        (sutherlandCanonicalCoordinates25 x y).w =
      sutherlandCanonicalCubicCofactor25 x y *
        sutherlandX1Plane25 x y := by
  simp only [sutherlandCanonicalCoordinates25, sutherlandCanonicalX25,
    sutherlandCanonicalXCore25, sutherlandCanonicalY25,
    sutherlandCanonicalZ25, sutherlandCanonicalW25,
    sutherlandCanonicalWCore25, sutherlandCanonicalCubicCofactor25, sutherlandCanonicalCubicCofactor25CoefficientTen, sutherlandCanonicalCubicCofactor25CoefficientNine, sutherlandCanonicalCubicCofactor25CoefficientEight, sutherlandCanonicalCubicCofactor25CoefficientSeven, sutherlandCanonicalCubicCofactor25CoefficientSix, sutherlandCanonicalCubicCofactor25CoefficientFive, sutherlandCanonicalCubicCofactor25CoefficientFour, sutherlandCanonicalCubicCofactor25CoefficientThree, sutherlandCanonicalCubicCofactor25CoefficientTwo, sutherlandCanonicalCubicCofactor25CoefficientOne, sutherlandCanonicalCubicCofactor25CoefficientZero,
    sutherlandX1Plane25, canonicalCubic25]
  ring

/-- Every affine point of Sutherland's optimized source equation maps to the
stored canonical quadric-cubic complete intersection.  Nonzeroness of the
homogeneous coordinate vector is intentionally handled separately. -/
theorem sutherlandCanonicalCoordinates25_onCanonical
    {x y : ℚ} (hsource : sutherlandX1Plane25 x y = 0) :
    OnCanonical25 (sutherlandCanonicalCoordinates25 x y) := by
  constructor
  · rw [sutherlandCanonicalCoordinates25_quadric, hsource, mul_zero]
  · rw [sutherlandCanonicalCoordinates25_cubic, hsource, mul_zero]

/-- Every primitive order-25 Tate solution maps to the canonical complete
intersection.  The assumptions are precisely the nonzero Tate parameter, the
proper-order-five exclusion, and the primitive factor equation. -/
theorem _root_.solution
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    OnCanonical25 (tateCanonicalCoordinates25 b c) := by
  apply sutherlandCanonicalCoordinates25_onCanonical
  simpa [tateSutherlandXCoordinate25, tateSutherlandYCoordinate25] using
    (tateToSutherland_on_plane hb h5 hF)

end MazurProof.RationalPointsN25CanonicalSourceBridge
