-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_at_yDen_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:59.044207+00:00
-- url     : https://prove2.me/submissions/2ed185c1-2734-4f02-bd7d-e96b8380e3cf

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

/-- On the divisor `s²-s-r+1=0`, parametrized by `r=s²-s+1`, the raw
equation reduces to `-s(s-1)²⁷`. -/
theorem _root_.solution (s : ℚ) :
    sutherlandRawX1Plane25 (s ^ 2 - s + 1) s = -(s * (s - 1) ^ 27) := by
  simp only [sutherlandRawX1Plane25, sutherlandRawCoefficientTen, sutherlandRawCoefficientNine, sutherlandRawCoefficientEight, sutherlandRawCoefficientSeven, sutherlandRawCoefficientSix, sutherlandRawCoefficientFive, sutherlandRawCoefficientFour, sutherlandRawCoefficientThree, sutherlandRawCoefficientTwo, sutherlandRawCoefficientOne, sutherlandRawCoefficientZero]
  ring

end MazurProof.RationalPointsN25SutherlandBridge
