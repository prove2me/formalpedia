-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientWeilThree.ternary_extension_cardinalities
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:24.01221+00:00
-- url     : https://prove2.me/submissions/65d7ce71-17cf-417f-a403-d82482e6c050

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

/-- The four executable models have cardinalities `3`, `9`, `27`, and `81`. -/
theorem _root_.solution :
    Fintype.card Trit = 3 ∧ Fintype.card F9 = 9 ∧
      Fintype.card F27 = 27 ∧ Fintype.card F81 = 81 := by
  decide +kernel

end MazurProof.RationalPointsN25QuotientWeilThree

namespace MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientWeilThree

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

section Elimination

variable {K : Type*} [Field K] [CharP K 3]

end Elimination

end MazurProof.RationalPointsN25QuotientWeilThreeLinear
