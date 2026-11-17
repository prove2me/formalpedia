-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerA25_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:05.003939+00:00
-- url     : https://prove2.me/submissions/9152385e-5a5a-4a99-b69e-636f9298ff49

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

/-- The stored coefficient `A` agrees with the structural Kummer
coefficient.  The conversion from `-1` to `2` uses characteristic three. -/
theorem _root_.solution :
    segreCoefficientA25Three f81FifthRoot25 = f81KummerA25 := by
  rcases f81_kummer_constants_correct with ⟨-, -, h, -⟩
  rw [ternaryPow_f81Operations_eq_pow,
    f81Operations_neg_eq, f81Operations_mul_eq,
    f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_one_eq] at h
  unfold segreCoefficientA25Three
  linear_combination h + f81FifthRoot25 ^ 3 * CharP.cast_eq_zero F81 3

end MazurProof.RationalPointsN25QuotientKummerThreeF81
