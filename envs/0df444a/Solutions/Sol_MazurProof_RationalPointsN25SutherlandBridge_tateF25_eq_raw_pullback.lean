-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.tateF25_eq_raw_pullback
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:00.104576+00:00
-- url     : https://prove2.me/submissions/fd9bcd0f-9c14-4727-9aff-5a1b64d9ecf7

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandRawPlaneEvaluations` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- Exact pullback of Sutherland's raw equation to the Tate chart.  The factors
`c¹⁰(b-c)¹⁵` account for clearing `r=b/c` and `s=c²/(b-c)`; no further
polynomial cofactor is present. -/
theorem _root_.solution (b c : ℚ) (hc : c ≠ 0) (hd : b - c ≠ 0) :
    F25 b c = c ^ 10 * (b - c) ^ 15 * sutherlandRawX1Plane25 (b / c) (c ^ 2 / (b - c)) := by
  simp only [sutherlandRawX1Plane25, sutherlandRawCoefficientTen, sutherlandRawCoefficientNine, sutherlandRawCoefficientEight, sutherlandRawCoefficientSeven, sutherlandRawCoefficientSix, sutherlandRawCoefficientFive, sutherlandRawCoefficientFour, sutherlandRawCoefficientThree, sutherlandRawCoefficientTwo, sutherlandRawCoefficientOne, sutherlandRawCoefficientZero, F25, F25DegreeTwentyFive, F25DegreeTwentySix, F25DegreeTwentySeven, F25DegreeTwentyEight, F25DegreeTwentyNine, F25DegreeThirty, F25DegreeThirtyOne, F25DegreeThirtyTwo, F25DegreeThirtyThree, F25DegreeThirtyFour, F25DegreeThirtyFive, F25DegreeThirtySix, F25DegreeThirtySeven, F25DegreeThirtyEight, F25DegreeThirtyNine, F25DegreeForty]
  field_simp
  ring

end MazurProof.RationalPointsN25SutherlandBridge
