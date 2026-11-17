-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandYDen_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:38.023223+00:00
-- url     : https://prove2.me/submissions/4f7b26f4-4280-4b6a-8d7d-9d0251de6347

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateR_ne_one
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_zero_of_tate
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandS_ne_one_on_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandYDen_ne_zero_on_raw

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandNonvanishing` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- The simplified denominator `B` of the optimized `y` coordinate is nonzero
on the primitive Tate locus.  Removing `c(b-c)²` reduces the claim to the
raw-model denominator `s²-s-r+1`. -/
theorem _root_.solution {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : tateToSutherlandYDen25 b c ≠ 0 := by
  have hraw := sutherlandRawX1Plane25_zero_of_tate hF hc hd
  have hs0 : c ^ 2 / (b - c) ≠ 0 := div_ne_zero (pow_ne_zero 2 hc) hd
  have hs1 := sutherlandS_ne_one_on_raw hraw (tateR_ne_one hc hd)
  have hBraw := sutherlandYDen_ne_zero_on_raw hraw hs0 hs1
  intro hB
  apply hBraw
  have hnum :
      c * (b - c) ^ 2 *
          ((c ^ 2 / (b - c)) ^ 2 - c ^ 2 / (b - c) - b / c + 1) = tateToSutherlandYDen25 b c := by
    field_simp
    simp [tateToSutherlandYDen25]
    ring
  rw [hB] at hnum
  exact (mul_eq_zero.mp hnum).resolve_left
    (mul_ne_zero hc (pow_ne_zero 2 hd))

end MazurProof.RationalPointsN25SutherlandBridge
