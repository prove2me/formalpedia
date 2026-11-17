-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerNumerator25_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:06.727016+00:00
-- url     : https://prove2.me/submissions/8a35c6fa-74b1-4f00-ae4e-02b37c3d60a7

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
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerB25_eq
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81FifthRootSq25_eq

/-! Kummer fibre counts of the canonical model over the explicit 81-element field. -/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientKummerThree

open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- The executable numerator is the numerator in the structural Kummer
model over the actual field `F81`. -/
theorem _root_.solution (t : F81) :
    f81KummerNumerator25 t =
      canonicalKummerNumerator25Three f81FifthRoot25 t := by
  unfold f81KummerNumerator25 canonicalKummerNumerator25Three
  rw [f81Operations_mul_eq, f81Operations_mul_eq,
    f81Operations_add_eq, f81Operations_mul_eq,
    f81KummerB25_eq, f81FifthRootSq25_eq]
  ring

end MazurProof.RationalPointsN25QuotientKummerThreeF81
