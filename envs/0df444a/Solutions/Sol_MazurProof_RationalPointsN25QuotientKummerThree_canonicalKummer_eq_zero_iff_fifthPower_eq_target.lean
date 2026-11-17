-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThree.canonicalKummer_eq_zero_iff_fifthPower_eq_target
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:14.388712+00:00
-- url     : https://prove2.me/submissions/59d2e4d5-60d2-40e8-96ae-8b16416e666e

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_ExplicitKummerThree

/-! Segre factorization and eigencoordinate identities for the canonical curve in characteristic three. -/

namespace MazurProof.RationalPointsN25QuotientKummerThree

open RationalPointsN25QuotientF2

section StructuralModel

variable {K : Type*} [Field K] [CharP K 3]

omit [CharP K 3] in
/-- On a nondegenerate quotient fibre, the Kummer polynomial vanishes
exactly when `r⁵` equals the normalized target.

This is a field identity: move the constant term to the right and divide by
the nonzero coefficient of `r⁵`. -/
theorem _root_.solution
    (e t : K) {r : K}
    (hden : canonicalKummerDenominator25Three e t ≠ 0) :
    canonicalKummerPolynomial25Three e r t = 0 ↔
      r ^ 5 = canonicalKummerTarget25Three e t := by
  unfold canonicalKummerTarget25Three
  rw [eq_div_iff hden]
  change r ^ 5 * canonicalKummerDenominator25Three e t +
      canonicalKummerNumerator25Three e t = 0 ↔
    r ^ 5 * canonicalKummerDenominator25Three e t =
      -canonicalKummerNumerator25Three e t
  constructor <;> intro h <;> linear_combination h

end StructuralModel

section FifthPowerFibres

open scoped Pointwise

end FifthPowerFibres

end MazurProof.RationalPointsN25QuotientKummerThree
