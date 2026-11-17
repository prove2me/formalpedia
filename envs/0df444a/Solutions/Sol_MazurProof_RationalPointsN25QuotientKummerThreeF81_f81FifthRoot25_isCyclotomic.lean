-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81FifthRoot25_isCyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:03.976847+00:00
-- url     : https://prove2.me/submissions/617383cb-96d1-4afe-9e37-b495b2c388aa

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
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81_kummer_constants_correct

/-! Kummer fibre counts of the canonical model over the explicit 81-element field. -/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientKummerThree

open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- The stored element `f81FifthRoot25` satisfies the fifth cyclotomic
equation in the transported characteristic-three field. -/
theorem _root_.solution :
    IsCyclotomicFive25Three f81FifthRoot25 := by
  rcases f81_kummer_constants_correct with ⟨h, -, -, -⟩
  rw [ternaryPow_f81Operations_eq_pow,
    ternaryPow_f81Operations_eq_pow,
    ternaryPow_f81Operations_eq_pow,
    f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_one_eq, f81Operations_zero_eq] at h
  exact h

end MazurProof.RationalPointsN25QuotientKummerThreeF81
