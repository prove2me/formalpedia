-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81FifthRootSq25_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:04.460857+00:00
-- url     : https://prove2.me/submissions/beebe460-dbcc-4f65-ac71-7d6282c28615

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

/-- The stored square literal is the actual square of the cyclotomic root. -/
theorem _root_.solution :
    f81FifthRoot25 ^ 2 = f81FifthRootSq25 := by
  rcases f81_kummer_constants_correct with ⟨-, h, -, -⟩
  rw [ternaryPow_f81Operations_eq_pow] at h
  exact h

end MazurProof.RationalPointsN25QuotientKummerThreeF81
