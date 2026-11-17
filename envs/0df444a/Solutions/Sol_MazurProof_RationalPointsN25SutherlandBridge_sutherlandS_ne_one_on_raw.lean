-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.sutherlandS_ne_one_on_raw
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:35.215193+00:00
-- url     : https://prove2.me/submissions/865af102-ac3b-41a0-805c-dfe0cb7c285d

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_at_s_one

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandNonvanishing` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- A raw point with `r≠1` cannot lie on `s=1`, because the raw equation then
equals `(r-1)¹⁰`. -/
theorem _root_.solution {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0) (hr1 : r ≠ 1) : s ≠ 1 := by
  intro hs
  subst s
  rw [sutherlandRawX1Plane25_at_s_one] at hraw
  exact hr1 (sub_eq_zero.mp
    ((pow_eq_zero_iff (by norm_num : (10 : ℕ) ≠ 0)).mp hraw))

end MazurProof.RationalPointsN25SutherlandBridge
