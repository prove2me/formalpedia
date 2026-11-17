-- Prove2me | solution 1 for N25.unitPlanePointPlace25_degree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:04.469665+00:00
-- url     : https://prove2.me/submissions/f15f368f-4822-4231-b71e-e7ffa9707fa5

import Definitions.Def_N25_UnitPlanePointPlace

noncomputable section

namespace N25

/-- The rational plane point defines a degree-one place of the actual plane
function field. The residue identification respects the rational constants. -/
theorem _root_.solution (u v : ℚ)
    (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    (unitPlanePointPlace25 u v hr hu).deg = 1 := by
  let h := unitPlanePointLocalRing25_isDVR u v hr hu
  letI : IsDomain (UnitPlanePointLocalRing25 u v hr) := Classical.choose h
  letI : IsDiscreteValuationRing (UnitPlanePointLocalRing25 u v hr) := Classical.choose_spec h
  change (AlgebraicCurve.placeOfDiscreteValuationRing ℚ
    (UnitPlanePointLocalRing25 u v hr) UnitPlaneFF25).deg = 1
  calc
    _ = Module.finrank ℚ (IsLocalRing.ResidueField (UnitPlanePointLocalRing25 u v hr)) :=
      (AlgebraicCurve.discreteValuationRingPlaceResidueAlgEquiv ℚ
        (UnitPlanePointLocalRing25 u v hr) UnitPlaneFF25).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℚ ℚ := (unitPlanePointResidueAlgEquiv25 u v hr).toLinearEquiv.finrank_eq
    _ = 1 := by simp

end N25
