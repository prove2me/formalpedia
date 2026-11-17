-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_actual_fiber_sum
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:17:34.977292+00:00
-- url     : https://prove2.me/submissions/df2635c1-10e8-4e18-87fb-1cecf7c54338

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
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81_kummer_fiber_sum
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81_kummer_actual_fiber_card

/-! Kummer fibre counts of the canonical model over the explicit 81-element field. -/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientKummerThree

open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- Summing actual root cardinalities over all quotient parameters gives 87
Kummer pairs.  The finite certificate is therefore attached to the genuine
field equation, not merely to the executable classifier. -/
theorem _root_.solution :
    ∑ t : F81,
      Nat.card {r : F81 //
        r ^ 5 * canonicalKummerDenominator25Three f81FifthRoot25 t +
          canonicalKummerNumerator25Three f81FifthRoot25 t = 0} = 87 := by
  simp_rw [f81_kummer_actual_fiber_card]
  exact f81_kummer_fiber_sum

end MazurProof.RationalPointsN25QuotientKummerThreeF81
