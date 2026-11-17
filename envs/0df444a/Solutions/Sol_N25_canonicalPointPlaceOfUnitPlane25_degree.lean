-- Prove2me | solution 1 for N25.canonicalPointPlaceOfUnitPlane25_degree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:45.846771+00:00
-- url     : https://prove2.me/submissions/91a8c787-8523-4dfe-9cdb-85794a8c426d

import Definitions.Def_N25_UnitPlanePointPlace
import Theorems.Thm_N25_unitPlanePointPlace25_degree

noncomputable section

namespace N25

/-- The birational field isomorphism transports the degree-one plane place to
an actual degree-one place of the canonical function field. -/
theorem _root_.solution (u v : ℚ)
    (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    (canonicalPointPlaceOfUnitPlane25 u v hr hu).deg = 1 := by
  calc
    _ = (unitPlanePointPlace25 u v hr hu).deg :=
      (AlgebraicCurve.Place.mapResidueAlgEquiv canonicalUnitPlaneAlgEquiv25
        (unitPlanePointPlace25 u v hr hu)).toLinearEquiv.finrank_eq.symm
    _ = 1 := unitPlanePointPlace25_degree u v hr hu

end N25
