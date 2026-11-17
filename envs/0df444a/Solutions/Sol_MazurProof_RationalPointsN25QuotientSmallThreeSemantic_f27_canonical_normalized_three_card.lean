-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f27_canonical_normalized_three_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:20.629184+00:00
-- url     : https://prove2.me/submissions/9730208c-cac7-4703-9866-53db4cb3be90

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Definitions.Def_N25_ExplicitSmallThreeSemantic
import Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThreeLinear_canonicalStructuredPointCount25F27_eq
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmallThreeSemantic_f27Operations_eq_field
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmallThreeSemantic_canonicalStructuredPointCount25Three_field_eq_card

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

/-- The canonical normalized curve has twenty points over the actual field
`F27`. -/
theorem _root_.solution :
    Nat.card {P : NormalizedProjective4 F27 // IsCanonicalNormalizedThree P} = 20 := by
  rw [← canonicalStructuredPointCount25Three_field_eq_card F27]
  rw [← f27Operations_eq_field]
  exact canonicalStructuredPointCount25F27_eq

end

end MazurProof.RationalPointsN25QuotientSmallThreeSemantic
