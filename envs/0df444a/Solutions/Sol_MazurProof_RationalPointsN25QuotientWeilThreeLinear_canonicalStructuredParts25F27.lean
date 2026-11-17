-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredParts25F27
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:59.995193+00:00
-- url     : https://prove2.me/submissions/cc342d95-1f21-4bcc-90b5-69aa97bbec1d

import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitWeilThreeLinear

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

/-- Over `F_27`, linear elimination leaves seventeen regular pairs and no
exceptional point. -/
theorem _root_.solution :
    (canonicalRegularPairs25Three f27Operations).card = 17 ∧
    (canonicalExceptionalPairs25Three f27Operations).card = 0 ∧
    (canonicalYChartPairs25Three f27Operations).card = 1 ∧
    (canonicalZChartValues25Three f27Operations).card = 1 := by


      decide +kernel

end MazurProof.RationalPointsN25QuotientWeilThreeLinear
