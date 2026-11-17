-- Prove2me | solution 1 for N25.unitPlaneFieldPointLift25C_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:36.045374+00:00
-- url     : https://prove2.me/submissions/d9b38ba8-d023-4217-917e-ab469bb290d8

import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Theorems.Thm_N25_unitPlaneFieldPointLift25C_algebraMap

/-! The coordinate formulas for universal unit-plane function-field evaluation. -/
namespace N25

/-- The two plane coordinates evaluate to the prescribed field-valued point. -/
theorem _root_.solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental K u) :
    unitPlaneFieldPointLift25C (K := K) u v hr hu
      (algebraMap (UnitPlaneRing25C K) (UnitPlaneFF25C K) (unitPlaneU25C K)) = u ∧
    unitPlaneFieldPointLift25C (K := K) u v hr hu
      (algebraMap (UnitPlaneRing25C K) (UnitPlaneFF25C K) (unitPlaneV25C K)) = v := by
  simp only [unitPlaneFieldPointLift25C_algebraMap]
  simp [unitPlaneFieldPointEvaluation25C, unitPlaneU25C, unitPlaneV25C,
    AdjoinRoot.algebraMap_eq]

end N25
