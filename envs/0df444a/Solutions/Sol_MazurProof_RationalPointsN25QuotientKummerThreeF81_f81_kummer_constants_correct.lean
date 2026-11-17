-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_constants_correct
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:13.035095+00:00
-- url     : https://prove2.me/submissions/fc687d34-ea06-443d-813a-986daa983aa4

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

/-- The explicit root and coefficient literals satisfy the cyclotomic and
coefficient identities used by the symbolic Kummer reduction.  This is a
constant-size check in the chosen polynomial basis. -/
theorem _root_.solution :
    let O := f81Operations
    let e := f81FifthRoot25
    let eSq := ternaryPow O e 2
    let eCube := ternaryPow O e 3
    let eFourth := ternaryPow O e 4
    O.add (O.add (O.add (O.add eFourth eCube) eSq) e) O.one = O.zero ∧
    eSq = f81FifthRootSq25 ∧
    O.add (O.add (O.mul (O.neg O.one) eCube) e) O.one = f81KummerA25 ∧
    O.add (O.add (O.add eCube (O.neg eSq)) (O.neg e)) O.one =
      f81KummerB25 := by
  decide +kernel

end MazurProof.RationalPointsN25QuotientKummerThreeF81
