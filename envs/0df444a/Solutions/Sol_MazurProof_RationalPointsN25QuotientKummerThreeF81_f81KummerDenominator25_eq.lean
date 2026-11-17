-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerDenominator25_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:06.087888+00:00
-- url     : https://prove2.me/submissions/7291168d-3f52-422c-9ff2-35621291accc

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
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerA25_eq

/-! Kummer fibre counts of the canonical model over the explicit 81-element field. -/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientKummerThree

open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- The executable denominator is the denominator in the structural Kummer
model over the actual field `F81`. -/
theorem _root_.solution (t : F81) :
    f81KummerDenominator25 t =
      canonicalKummerDenominator25Three f81FifthRoot25 t := by
  unfold f81KummerDenominator25 canonicalKummerDenominator25Three
  rw [f81Operations_add_eq, f81Operations_mul_eq,
    f81Operations_one_eq, f81KummerA25_eq]

end MazurProof.RationalPointsN25QuotientKummerThreeF81
