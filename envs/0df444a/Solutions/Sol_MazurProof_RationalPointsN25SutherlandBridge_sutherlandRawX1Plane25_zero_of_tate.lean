-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_zero_of_tate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:36.383038+00:00
-- url     : https://prove2.me/submissions/9afacee5-e65e-4bdb-906c-45fd6e8c5458

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateF25_eq_raw_pullback

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandNonvanishing` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- A primitive Tate zero maps to a zero of Sutherland's raw equation whenever
the two Tate-chart denominators `c` and `b-c` are nonzero. -/
theorem _root_.solution {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : sutherlandRawX1Plane25 (b / c) (c ^ 2 / (b - c)) = 0 := by
  have hpull := tateF25_eq_raw_pullback b c hc hd
  rw [hF] at hpull
  have hp : c ^ 10 * (b - c) ^ 15 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 10 hc) (pow_ne_zero 15 hd)
  exact (mul_eq_zero.mp hpull.symm).resolve_left hp

end MazurProof.RationalPointsN25SutherlandBridge
