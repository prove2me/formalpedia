-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmallThreeSemantic.canonicalStructuredPointCount25Three_field_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:18.155919+00:00
-- url     : https://prove2.me/submissions/fbe46e66-753e-480b-96a0-ae85703142f8

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Definitions.Def_N25_ExplicitSmallThreeSemantic
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs

/-! Canonical normalized point counts over the explicit fields with 3, 9 and 27 elements. -/

namespace MazurProof.RationalPointsN25QuotientSmallThreeSemantic

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeilThree

open MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

noncomputable section

universe u

/-- The structural count is the cardinality of the semantic normalized curve
over every finite field of characteristic three. -/
theorem _root_.solution
    (K : Type u) [Field K] [CharP K 3] [Fintype K] [DecidableEq K] :
    canonicalStructuredPointCount25Three (fieldTernaryOperations K) =
      Nat.card {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P} := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr (canonicalCurveEquivStructured25Three K)]
  simp [CanonicalStructuredSolutions25Three,
    canonicalStructuredPointCount25Three, Fintype.card_coe]
  omega

end

end MazurProof.RationalPointsN25QuotientSmallThreeSemantic
