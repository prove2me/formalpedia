-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerB25_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:05.495285+00:00
-- url     : https://prove2.me/submissions/94c2e5b8-eae6-45e3-9c26-a76e91810e3a

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

/-- The stored coefficient `B` agrees with the structural Kummer
coefficient, again interpreting the table's negative signs in
characteristic three. -/
theorem _root_.solution :
    segreCoefficientB25Three f81FifthRoot25 = f81KummerB25 := by
  rcases f81_kummer_constants_correct with ⟨-, -, -, h⟩
  rw [ternaryPow_f81Operations_eq_pow,
    ternaryPow_f81Operations_eq_pow,
    f81Operations_neg_eq, f81Operations_neg_eq,
    f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_add_eq, f81Operations_one_eq] at h
  unfold segreCoefficientB25Three
  linear_combination h + (f81FifthRoot25 ^ 2 + f81FifthRoot25) *
    CharP.cast_eq_zero F81 3

end MazurProof.RationalPointsN25QuotientKummerThreeF81
