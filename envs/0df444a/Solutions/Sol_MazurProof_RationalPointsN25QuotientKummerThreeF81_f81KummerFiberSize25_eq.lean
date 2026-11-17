-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerFiberSize25_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:07.296206+00:00
-- url     : https://prove2.me/submissions/30765215-f63d-4fc9-b6d9-11f822c4bcb4

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
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerNumerator25_eq
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerDenominator25_eq
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerTarget25_eq

/-! Kummer fibre counts of the canonical model over the explicit 81-element field. -/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientKummerThree

open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- The executable fibre classifier is exactly the generic 81-element-field
classifier; the table is no longer a separate, untyped computation. -/
theorem _root_.solution (t : F81) :
    f81KummerFiberSize25 t =
      canonicalKummerFiberSizeField81 f81FifthRoot25 t := by
  unfold f81KummerFiberSize25 canonicalKummerFiberSizeField81
  rw [f81KummerDenominator25_eq, f81KummerNumerator25_eq]
  simp only [f81Operations_zero_eq, f81Operations_one_eq,
    f81KummerTarget25_eq, ternaryPow_f81Operations_eq_pow,
    canonicalKummerTarget25Three]

end MazurProof.RationalPointsN25QuotientKummerThreeF81
