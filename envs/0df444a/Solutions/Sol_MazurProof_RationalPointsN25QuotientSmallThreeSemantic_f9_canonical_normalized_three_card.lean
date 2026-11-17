-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f9_canonical_normalized_three_card
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:33.386793+00:00
-- url     : https://prove2.me/submissions/182f4bf8-d08c-49b9-9814-ab64d74afadd

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Definitions.Def_N25_ExplicitSmallThreeSemantic
import Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThreeLinear_canonicalStructuredPointCount25F9_eq
import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmallThreeSemantic_f9Operations_eq_field
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

/-- The canonical normalized curve has five points over the actual field
`F9`. -/
theorem _root_.solution :
    Nat.card {P : NormalizedProjective4 F9 // IsCanonicalNormalizedThree P} = 5 := by
  rw [← canonicalStructuredPointCount25Three_field_eq_card F9]
  rw [← f9Operations_eq_field]
  exact canonicalStructuredPointCount25F9_eq

end

end MazurProof.RationalPointsN25QuotientSmallThreeSemantic
