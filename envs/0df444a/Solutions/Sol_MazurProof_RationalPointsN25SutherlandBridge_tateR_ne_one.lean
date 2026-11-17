-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.tateR_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:36.937203+00:00
-- url     : https://prove2.me/submissions/b4db5cbb-e919-4152-ae67-0bd1fac0745a

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandNonvanishing` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- The raw coordinate `r=b/c` is not `1` when `c≠0` and the proper-order-five
factor `b-c` is nonzero. -/
theorem _root_.solution {b c : ℚ} (hc : c ≠ 0) (hd : b - c ≠ 0) : b / c ≠ 1 := by
  intro h
  apply hd
  field_simp at h
  linarith

end MazurProof.RationalPointsN25SutherlandBridge
