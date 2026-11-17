-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.tateC_ne_zero_of_F25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:59.598668+00:00
-- url     : https://prove2.me/submissions/b4129cef-0823-48ac-ad6d-3ada8698f628

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

/-- On a nonzero Tate parameter `b`, a zero of `F25` necessarily has `c≠0`:
the specialization `F25(b,0)` is `b²⁵`. -/
theorem _root_.solution {b c : ℚ} (hb : b ≠ 0) (hF : F25 b c = 0) : c ≠ 0 := by
  intro hc
  subst c
  simp [F25, F25DegreeTwentyFive, F25DegreeTwentySix, F25DegreeTwentySeven, F25DegreeTwentyEight, F25DegreeTwentyNine, F25DegreeThirty, F25DegreeThirtyOne, F25DegreeThirtyTwo, F25DegreeThirtyThree, F25DegreeThirtyFour, F25DegreeThirtyFive, F25DegreeThirtySix, F25DegreeThirtySeven, F25DegreeThirtyEight, F25DegreeThirtyNine, F25DegreeForty] at hF
  exact hb hF

end MazurProof.RationalPointsN25SutherlandBridge
