-- Prove2me | solution 1 for N25.unitPlaneFieldPointLift25C_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:35.155279+00:00
-- url     : https://prove2.me/submissions/b98457b5-c4eb-4102-9836-924f90f7e6f8

import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField

/-! The coordinate formulas for universal unit-plane function-field evaluation. -/
namespace N25

/-- Function-field evaluation extends the coordinate-ring point map. -/
theorem _root_.solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental K u)
    (a : UnitPlaneRing25C K) :
    unitPlaneFieldPointLift25C (K := K) u v hr hu
      (algebraMap (UnitPlaneRing25C K) (UnitPlaneFF25C K) a) =
      unitPlaneFieldPointEvaluation25C (K := K) u v hr a := by
  exact IsFractionRing.lift_algebraMap
    (unitPlaneFieldPointEvaluation25C_injective (K := K) u v hr hu) a

end N25
