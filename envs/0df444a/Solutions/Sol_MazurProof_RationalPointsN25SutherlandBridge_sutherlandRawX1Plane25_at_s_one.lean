-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_at_s_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:34.686598+00:00
-- url     : https://prove2.me/submissions/33aeb7cc-a3b4-4fee-a116-b1fc32ca3670

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

/-- The boundary specialization `s=1` of the raw model is the single cusp
factor `(r-1)¹⁰`. -/
theorem _root_.solution (r : ℚ) : sutherlandRawX1Plane25 r 1 = (r - 1) ^ 10 := by
  simp [sutherlandRawX1Plane25, sutherlandRawCoefficientTen, sutherlandRawCoefficientNine, sutherlandRawCoefficientEight, sutherlandRawCoefficientSeven, sutherlandRawCoefficientSix, sutherlandRawCoefficientFive, sutherlandRawCoefficientFour, sutherlandRawCoefficientThree, sutherlandRawCoefficientTwo, sutherlandRawCoefficientOne, sutherlandRawCoefficientZero]
  ring

end MazurProof.RationalPointsN25SutherlandBridge
