-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandCommon_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:37.494044+00:00
-- url     : https://prove2.me/submissions/678ca866-703d-4469-8ea5-37613b6bd55b

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandCommon_ne_zero_on_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateR_ne_one
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_zero_of_tate

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandNonvanishing` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- The simplified common factor `K` is nonzero on the primitive Tate locus.
After removing the nonzero scalar `c(b-c)`, this is the raw-model denominator
`r*s-2*r+1`, whose vanishing was excluded above. -/
theorem _root_.solution {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : tateToSutherlandCommon25 b c ≠ 0 := by
  have hraw := sutherlandRawX1Plane25_zero_of_tate hF hc hd
  have hA := sutherlandCommon_ne_zero_on_raw hraw (tateR_ne_one hc hd)
  intro hK
  apply hA
  have hnum :
      c * (b - c) * ((b / c) * (c ^ 2 / (b - c)) - 2 * (b / c) + 1) = tateToSutherlandCommon25 b c := by
    field_simp
    simp [tateToSutherlandCommon25]
    ring
  rw [hK] at hnum
  exact (mul_eq_zero.mp hnum).resolve_left (mul_ne_zero hc hd)

end MazurProof.RationalPointsN25SutherlandBridge
