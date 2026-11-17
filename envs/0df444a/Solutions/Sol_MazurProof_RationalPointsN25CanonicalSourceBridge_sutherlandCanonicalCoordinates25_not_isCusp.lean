-- Prove2me | solution 1 for MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalCoordinates25_not_isCusp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:03.405445+00:00
-- url     : https://prove2.me/submissions/e83a7bdc-bdac-42a5-a25e-53ec2cb6195d

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
import Theorems.Thm_MazurProof_RationalPointsN25QuotientAction_isCusp25_iff
import Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandBasePointFiber25_ne_zero
import Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandCanonicalXW_not_both_zero

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_CanonicalZCoordinate` and their helpers. -/

namespace MazurProof.RationalPointsN25CanonicalSourceBridge

open RationalPointsN25CanonicalPoints

open RationalPointsN25QuotientAction

open RationalPointsN25SutherlandBridge

open TateOrder25Factor

/-- Exact resultant identity between the source equation and the third
canonical coordinate.  Its only fibre factors are the excluded chart boundary
`y=1` and the degree-ten polynomial with no rational root. -/
theorem sutherlandCanonicalZ_bezout_identity25 (x y : ℚ) :
    sutherlandCanonicalZBezoutSource25 x y * sutherlandX1Plane25 x y +
        sutherlandCanonicalZBezoutCoordinate25 x y *
          sutherlandCanonicalZ25 x y =
      (y
    - 1) ^ 12 * sutherlandBasePointFiber25 y := by
  simp only [sutherlandCanonicalZBezoutSource25, sutherlandCanonicalZBezoutSource25CoefficientFive, sutherlandCanonicalZBezoutSource25CoefficientFour, sutherlandCanonicalZBezoutSource25CoefficientThree, sutherlandCanonicalZBezoutSource25CoefficientTwo, sutherlandCanonicalZBezoutSource25CoefficientOne, sutherlandCanonicalZBezoutSource25CoefficientZero,
    sutherlandCanonicalZBezoutCoordinate25, sutherlandX1Plane25,
    sutherlandCanonicalZ25, sutherlandBasePointFiber25, sutherlandCanonicalZBezoutCoordinate25CoefficientSeven, sutherlandCanonicalZBezoutCoordinate25CoefficientSix, sutherlandCanonicalZBezoutCoordinate25CoefficientFive, sutherlandCanonicalZBezoutCoordinate25CoefficientFour, sutherlandCanonicalZBezoutCoordinate25CoefficientThree, sutherlandCanonicalZBezoutCoordinate25CoefficientTwo, sutherlandCanonicalZBezoutCoordinate25CoefficientOne, sutherlandCanonicalZBezoutCoordinate25CoefficientZero]
  ring

/-- The third canonical coordinate never vanishes on the optimized source
away from `y=1`.  The exact resultant would otherwise force a rational root
of the degree-ten base-point fibre polynomial. -/
theorem sutherlandCanonicalZ25_ne_zero
    {x y : ℚ} (hsource : sutherlandX1Plane25 x y = 0) (hy1 : y ≠ 1) :
    sutherlandCanonicalZ25 x y ≠ 0 := by
  intro hZ
  have hbezout := sutherlandCanonicalZ_bezout_identity25 x y
  rw [hsource, hZ, mul_zero, mul_zero, zero_add] at hbezout
  have hySub : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
  have hfiber : sutherlandBasePointFiber25 y = 0 :=
    (mul_eq_zero.mp hbezout.symm).resolve_left (pow_ne_zero 12 hySub)
  exact sutherlandBasePointFiber25_ne_zero y hfiber

/-- A homogeneous vector cannot represent any canonical cusp when its third
coordinate is nonzero and its first and fourth coordinates do not vanish
simultaneously.  The third coordinate excludes cusps A, C, and E, while the
other two coordinates exclude B and D. -/
theorem not_isCusp25_of_z_ne_zero_and_xw
    {p : Coordinates25} (hz : p.z ≠ 0) (hxw : p.x ≠ 0 ∨ p.w ≠ 0) :
    ¬ IsCusp25 p := by
  intro hcusp
  rw [isCusp25_iff] at hcusp
  rcases hcusp with hpA | hpB | hpC | hpD | hpE
  · rcases hpA with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    exact hz (by simpa [cusp25A] using hpz)
  · rcases hpB with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    rcases hxw with hx | hw
    · exact hx (by simpa [cusp25B] using hpx)
    · exact hw (by simpa [cusp25B] using hpw)
  · rcases hpC with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    exact hz (by simpa [cusp25C] using hpz)
  · rcases hpD with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    rcases hxw with hx | hw
    · exact hx (by simpa [cusp25D] using hpx)
    · exact hw (by simpa [cusp25D] using hpw)
  · rcases hpE with ⟨a, ha, hpx, hpy, hpz, hpw⟩
    exact hz (by simpa [cusp25E] using hpz)

/-- Every optimized source point away from the boundary `y=1` maps outside
the five canonical cusp classes.  The source equation makes the third
coordinate nonzero, and the base-point certificate supplies the complementary
first/fourth nonvanishing condition. -/
theorem _root_.solution
    {x y : ℚ} (hsource : sutherlandX1Plane25 x y = 0) (hy1 : y ≠ 1) :
    ¬ IsCusp25 (sutherlandCanonicalCoordinates25 x y) := by
  apply not_isCusp25_of_z_ne_zero_and_xw
  · simpa [sutherlandCanonicalCoordinates25] using
      sutherlandCanonicalZ25_ne_zero hsource hy1
  · simpa [sutherlandCanonicalCoordinates25] using
      sutherlandCanonicalXW_not_both_zero (x := x) hy1

end MazurProof.RationalPointsN25CanonicalSourceBridge
