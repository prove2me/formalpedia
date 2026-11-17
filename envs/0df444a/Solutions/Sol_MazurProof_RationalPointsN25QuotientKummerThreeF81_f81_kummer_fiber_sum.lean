-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_fiber_sum
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:08.844012+00:00
-- url     : https://prove2.me/submissions/5e600649-44c0-43f9-8414-3e8e3a3b47e2

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

/-- The one-dimensional fibre sum contains 87 Kummer pairs. -/
theorem _root_.solution :
    ∑ t : F81, f81KummerFiberSize25 t = 87 := by

    decide +kernel

end MazurProof.RationalPointsN25QuotientKummerThreeF81
