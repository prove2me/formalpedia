-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandY_eq_raw
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:00.621592+00:00
-- url     : https://prove2.me/submissions/45afeee0-040f-4ee4-8824-acd33d7a8221

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandModel` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- The raw formula `(r*s-2*r+1)/(s²-s-r+1)` simplifies to `K(b-c)/B` in
Tate coordinates. -/
theorem _root_.solution
    {b c : ℚ} (hc : c ≠ 0) (hd : b - c ≠ 0)
    (hB : tateToSutherlandYDen25 b c ≠ 0) :
    ((b / c) * (c ^ 2 / (b - c)) - 2 * (b / c) + 1) /
        ((c ^ 2 / (b - c)) ^ 2 - c ^ 2 / (b - c) - b / c + 1) =
      tateToSutherlandCommon25 b c * (b - c) /
        tateToSutherlandYDen25 b c := by
  have hB' :
      -b ^ 3 + 3 * b ^ 2 * c - b * c ^ 3 - 3 * b * c ^ 2 +
          c ^ 5 + c ^ 4 + c ^ 3 ≠ 0 := by
    simpa [tateToSutherlandYDen25] using hB
  simp only [tateToSutherlandCommon25, tateToSutherlandYDen25]
  field_simp [hc, hd, hB']
  ring

end MazurProof.RationalPointsN25SutherlandBridge
