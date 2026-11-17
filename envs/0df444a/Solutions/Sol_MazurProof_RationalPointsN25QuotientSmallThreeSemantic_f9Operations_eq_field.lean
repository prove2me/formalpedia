-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f9Operations_eq_field
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:20.079325+00:00
-- url     : https://prove2.me/submissions/6471f57b-274c-46c9-973a-b93036832957

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

/-- The executable quadratic operation record is the operation record of its
certified field structure. -/
theorem _root_.solution :
    f9Operations = fieldTernaryOperations F9 := by
  rfl

end

end MazurProof.RationalPointsN25QuotientSmallThreeSemantic
