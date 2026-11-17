-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawToOptimized_bihomogeneous_identity
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:33.992865+00:00
-- url     : https://prove2.me/submissions/55017f9e-8a02-4843-841a-7b062bba4398

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandRawToOptimized` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- The raw-to-optimized comparison as a polynomial identity.  With
`X=s-r`, `K=r*s-2*r+1`, and `B=s²-s-r+1`, the bihomogenized optimized equation
is `(r-s)⁴(s-1)³K²` times the raw equation. -/
theorem _root_.solution (r s : ℚ) :
    sutherlandBihomogenized25
        (s - r) (r * s - 2 * r + 1) 1 (s ^ 2 - s - r + 1) =
      (r - s) ^ 4 * (s - 1) ^ 3 * (r * s - 2 * r + 1) ^ 2 *
        sutherlandRawX1Plane25 r s := by
  simp only [sutherlandBihomogenized25, sutherlandHomogeneousCoefficientEight, sutherlandHomogeneousCoefficientSeven, sutherlandHomogeneousCoefficientSix, sutherlandHomogeneousCoefficientFive, sutherlandHomogeneousCoefficientFour, sutherlandHomogeneousCoefficientThree, sutherlandHomogeneousCoefficientTwo, sutherlandHomogeneousCoefficientOne, sutherlandHomogeneousCoefficientZero, sutherlandRawX1Plane25, sutherlandRawCoefficientTen, sutherlandRawCoefficientNine, sutherlandRawCoefficientEight, sutherlandRawCoefficientSeven, sutherlandRawCoefficientSix, sutherlandRawCoefficientFive, sutherlandRawCoefficientFour, sutherlandRawCoefficientThree, sutherlandRawCoefficientTwo, sutherlandRawCoefficientOne, sutherlandRawCoefficientZero]
  ring

end MazurProof.RationalPointsN25SutherlandBridge
