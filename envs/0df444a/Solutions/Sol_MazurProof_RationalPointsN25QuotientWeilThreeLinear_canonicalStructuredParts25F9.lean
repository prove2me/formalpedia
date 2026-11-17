-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredParts25F9
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:00.617108+00:00
-- url     : https://prove2.me/submissions/6ece4c75-2e1d-4157-9f1b-6d17ec750bd2

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

/-- Over `F_9`, the regular residual locus again has two points and the
exceptional divisor has none. -/
theorem _root_.solution :
    (canonicalRegularPairs25Three f9Operations).card = 2 ∧
    (canonicalExceptionalPairs25Three f9Operations).card = 0 ∧
    (canonicalYChartPairs25Three f9Operations).card = 1 ∧
    (canonicalZChartValues25Three f9Operations).card = 1 := by

    decide +kernel

end MazurProof.RationalPointsN25QuotientWeilThreeLinear
