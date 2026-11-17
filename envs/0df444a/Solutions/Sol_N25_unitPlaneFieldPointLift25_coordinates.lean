-- Prove2me | solution 1 for N25.unitPlaneFieldPointLift25_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:03.809195+00:00
-- url     : https://prove2.me/submissions/834cc1a1-b8e0-4c2e-8108-63f77c88cc6d

import Definitions.Def_N25_UnitPlaneFieldPointLift
import Theorems.Thm_N25_unitPlaneFieldPointLift25_algebraMap

namespace N25

/-- The two universal generator formulas on the actual plane function field. -/
theorem _root_.solution {F : Type*} [Field F] [Algebra ℚ F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental ℚ u) :
    unitPlaneFieldPointLift25 u v hr hu (algebraMap UnitPlaneRing UnitPlaneFF25 unitPlaneU) = u ∧
    unitPlaneFieldPointLift25 u v hr hu (algebraMap UnitPlaneRing UnitPlaneFF25 unitPlaneV) = v := by
  simp only [unitPlaneFieldPointLift25_algebraMap]
  simp [unitPlaneFieldPointEvaluation25, unitPlaneU, unitPlaneV, AdjoinRoot.algebraMap_eq]

end N25
