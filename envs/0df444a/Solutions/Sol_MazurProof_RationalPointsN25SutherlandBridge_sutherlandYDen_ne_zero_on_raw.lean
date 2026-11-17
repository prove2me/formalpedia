-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.sutherlandYDen_ne_zero_on_raw
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:35.799649+00:00
-- url     : https://prove2.me/submissions/778c4c06-cf70-47df-bff7-4f3e7be8b73f

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_at_yDen_zero

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandNonvanishing` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- The second denominator `s²-s-r+1` is nonzero at a raw point with
`s≠0,1`.  Its vanishing specialization is exactly `-s(s-1)²⁷`. -/
theorem _root_.solution {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : s ^ 2 - s - r + 1 ≠ 0 := by
  intro hB
  have hr : r = s ^ 2 - s + 1 := by linarith
  have hid := sutherlandRawX1Plane25_at_yDen_zero s
  rw [← hr, hraw] at hid
  have hz : s * (s - 1) ^ 27 = 0 := by linarith
  rcases mul_eq_zero.mp hz with hs | hs
  · exact hs0 hs
  · exact hs1 (sub_eq_zero.mp
      ((pow_eq_zero_iff (by norm_num : (27 : ℕ) ≠ 0)).mp hs))

end MazurProof.RationalPointsN25SutherlandBridge
