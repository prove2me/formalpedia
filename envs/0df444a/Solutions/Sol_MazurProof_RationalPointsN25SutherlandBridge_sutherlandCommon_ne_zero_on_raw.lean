-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.sutherlandCommon_ne_zero_on_raw
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:58.214888+00:00
-- url     : https://prove2.me/submissions/f98fe1d7-792f-4e34-bfe8-82afcc8737bc

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

/-- On the divisor `r*s-2*r+1=0`, parametrized by `r=1/(2-s)`, the raw
equation reduces to `(s-1)²³` after clearing the tenth power denominator. -/
theorem sutherlandRawX1Plane25_at_common_zero (s : ℚ) (hs : 2 - s ≠ 0) :
    (2 - s) ^ 10 * sutherlandRawX1Plane25 (1 / (2 - s)) s = (s - 1) ^ 23 := by
  simp only [sutherlandRawX1Plane25, sutherlandRawCoefficientTen, sutherlandRawCoefficientNine, sutherlandRawCoefficientEight, sutherlandRawCoefficientSeven, sutherlandRawCoefficientSix, sutherlandRawCoefficientFive, sutherlandRawCoefficientFour, sutherlandRawCoefficientThree, sutherlandRawCoefficientTwo, sutherlandRawCoefficientOne, sutherlandRawCoefficientZero]
  field_simp
  ring

/-- The first denominator of the raw-to-optimized map cannot vanish at a raw
point away from `r=1`.  The preceding specialization forces `s=1`, after
which the denominator equation itself forces `r=1`. -/
theorem _root_.solution {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0) (hr1 : r ≠ 1) :
    r * s - 2 * r + 1 ≠ 0 := by
  intro hA
  have hs2 : 2 - s ≠ 0 := by
    intro hs2
    have hs : s = 2 := by linarith
    rw [hs] at hA
    linarith
  have hr : r = 1 / (2 - s) := by
    field_simp
    linarith
  have hid := sutherlandRawX1Plane25_at_common_zero s hs2
  rw [← hr, hraw, mul_zero] at hid
  have hs1 : s = 1 :=
    sub_eq_zero.mp
      ((pow_eq_zero_iff (by norm_num : (23 : ℕ) ≠ 0)).mp hid.symm)
  rw [hs1] at hA
  exact hr1 (by linarith)

end MazurProof.RationalPointsN25SutherlandBridge
