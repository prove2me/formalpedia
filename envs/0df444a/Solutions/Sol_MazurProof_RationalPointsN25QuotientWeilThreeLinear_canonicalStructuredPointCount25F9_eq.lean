-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredPointCount25F9_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:01.539751+00:00
-- url     : https://prove2.me/submissions/ff759431-a098-4b81-8afb-76db336c34de

import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThreeLinear_canonicalStructuredParts25F9

/-! Structured point counts of the canonical model over the explicit fields of characteristic three. -/

namespace MazurProof.RationalPointsN25QuotientWeilThree

open RationalPointsN25QuotientF2

open RationalPointsN25QuotientWeil

end MazurProof.RationalPointsN25QuotientWeilThree

namespace MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientWeilThree

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

section Elimination

variable {K : Type*} [Field K] [CharP K 3]

end Elimination

/-- The structural decomposition recovers `#C(F_9)=5`. -/
theorem _root_.solution :
    canonicalStructuredPointCount25Three f9Operations = 5 := by
  rcases canonicalStructuredParts25F9 with ⟨hR, hE, hY, hZ⟩
  simp [canonicalStructuredPointCount25Three, hR, hE, hY, hZ]

end MazurProof.RationalPointsN25QuotientWeilThreeLinear
