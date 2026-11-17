-- Prove2me | solution 1 for N25.canonicalChart_locallyStandardSmoothOfRelativeDimension_good25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:24.664108+00:00
-- url     : https://prove2.me/submissions/c76cc095-93fb-45a6-8680-e6c3d4f61bbd

import Mathlib
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_RingHom_Locally_isStandardSmoothOfRelativeDimension_of_jacobian_span
import Theorems.Thm_N25_canonicalChartPairPresentation25_dimension
import Theorems.Thm_N25_canonicalChartPairPresentation25_jacobian_span_good

/-! Smooth canonical charts, with relative dimension one from their literal presentations. -/
noncomputable section

namespace N25

/-- The literal chart map is locally standard smooth of relative dimension one. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] (i : Fin 4) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K (CanonicalChartRing25 K i)) :=
  RingHom.Locally.isStandardSmoothOfRelativeDimension_of_jacobian_span
    (canonicalChartPairPresentation25 K i) (canonicalChartPairPresentation25_dimension K i)
    (canonicalChartPairPresentation25_jacobian_span_good p hp K i)

end N25
