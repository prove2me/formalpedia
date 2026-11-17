-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerTarget25_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:12.46018+00:00
-- url     : https://prove2.me/submissions/cc2e21e6-6027-4d92-b41d-09b755b3f6df

import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Kummer fibre counts of the canonical model over the explicit 81-element field. -/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientKummerThree

open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- The normalized target computed by the executable table is the field
quotient used in the generic Kummer classifier. -/
theorem _root_.solution (t : F81) :
    f81Operations.mul
        (f81Operations.neg
          (canonicalKummerNumerator25Three f81FifthRoot25 t))
        (f81Inv (canonicalKummerDenominator25Three f81FifthRoot25 t)) =
      canonicalKummerTarget25Three f81FifthRoot25 t := by
  unfold canonicalKummerTarget25Three
  rw [f81Operations_mul_eq, f81Operations_neg_eq, f81Inv_eq_inv,
    div_eq_mul_inv]

end MazurProof.RationalPointsN25QuotientKummerThreeF81
