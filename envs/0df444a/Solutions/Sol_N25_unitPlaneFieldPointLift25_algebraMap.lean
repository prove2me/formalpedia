-- Prove2me | solution 1 for N25.unitPlaneFieldPointLift25_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:36.703197+00:00
-- url     : https://prove2.me/submissions/72e3218c-6417-429e-9d76-4ea9a46f20ae

import Definitions.Def_N25_UnitPlaneFieldPointLift

namespace N25

/-- The universal function-field map extends the actual coordinate-ring point map. -/
theorem _root_.solution {F : Type*} [Field F] [Algebra ℚ F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental ℚ u) (a : UnitPlaneRing) :
    unitPlaneFieldPointLift25 u v hr hu (algebraMap UnitPlaneRing UnitPlaneFF25 a) =
      unitPlaneFieldPointEvaluation25 u v hr a := by
  exact IsFractionRing.lift_algebraMap (unitPlaneFieldPointEvaluation25_injective u v hr hu) a

end N25
