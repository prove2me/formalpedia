-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_actual_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:09.470635+00:00
-- url     : https://prove2.me/submissions/ab24343a-316a-47f5-aeda-2ac8ff7d4623

import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
import Definitions.Def_N25_ExplicitKummerThreeF81
import Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThree_ternary_extension_cardinalities
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_canonicalKummerFiber_card_field81
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerFiberSize25_eq

/-! Kummer fibre counts of the canonical model over the explicit 81-element field. -/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientKummerThree

open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- For every quotient parameter, the executable number is the actual
cardinality of the Kummer equation's fifth-power fibre. -/
theorem _root_.solution (t : F81) :
    Nat.card {r : F81 //
      r ^ 5 * canonicalKummerDenominator25Three f81FifthRoot25 t +
        canonicalKummerNumerator25Three f81FifthRoot25 t = 0} =
      f81KummerFiberSize25 t := by
  rw [f81KummerFiberSize25_eq]
  exact canonicalKummerFiber_card_field81 (K := F81)
    (e := f81FifthRoot25) (t := t)
    (by
      rw [Nat.card_eq_fintype_card]
      exact ternary_extension_cardinalities.2.2.2)

end MazurProof.RationalPointsN25QuotientKummerThreeF81
