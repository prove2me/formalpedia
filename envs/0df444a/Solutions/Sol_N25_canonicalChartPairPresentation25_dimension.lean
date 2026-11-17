-- Prove2me | solution 1 for N25.canonicalChartPairPresentation25_dimension
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:01.228367+00:00
-- url     : https://prove2.me/submissions/0213129a-0fff-4bd1-9f80-77e7e49d65f2

import Mathlib
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Smooth canonical charts, with relative dimension one from their literal presentations. -/
noncomputable section

namespace N25

/-- The selected presentation has four variables and three relations. -/
theorem _root_.solution (K : Type*) [CommRing K]
    (pivot : Fin 4) (pair : CanonicalChartColumnPair25 pivot) :
    (canonicalChartPairPresentation25 K pivot pair).dimension = 1 := by
  simp [Algebra.Presentation.dimension]

end N25
