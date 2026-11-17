-- Prove2me | solution 1 for N25.canonicalPointPlaceOfUnitPlane25_unit_orders
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:48.311425+00:00
-- url     : https://prove2.me/submissions/2275963b-7b06-4cdc-bbe2-2f48aff74554

import Definitions.Def_N25_CanonicalFunctionCoordinates
import Definitions.Def_N25_CanonicalNoncuspPlace

/-! Noncuspidal canonical points make both distinguished functions local units. -/
noncomputable section

namespace N25

private theorem canonicalPointPlaceOfUnitPlane25_order_eq_zero
    (u v : ℚ) (hr : planeRelation u v = 0) (hu : u ≠ 0)
    (a : UnitPlaneRing) (ha : unitPlaneEvaluation25 u v hr a ≠ 0) :
    (canonicalPointPlaceOfUnitPlane25 u v hr hu).ord
      (canonicalUnitPlaneAlgEquiv25 (algebraMap UnitPlaneRing UnitPlaneFF25 a)) = 0 := by
  let h := unitPlanePointLocalRing25_isDVR u v hr hu
  letI : IsDomain (UnitPlanePointLocalRing25 u v hr) := Classical.choose h
  letI : IsDiscreteValuationRing (UnitPlanePointLocalRing25 u v hr) := Classical.choose_spec h
  let p := unitPlanePointPlace25 u v hr hu
  let a₀ := algebraMap UnitPlaneRing (UnitPlanePointLocalRing25 u v hr) a
  have hmem : a ∈ (unitPlanePointIdeal25 u v hr).primeCompl := by
    change unitPlaneEvaluation25 u v hr a ≠ 0
    exact ha
  have hunit : IsUnit a₀ :=
    IsLocalization.map_units (UnitPlanePointLocalRing25 u v hr) ⟨a, hmem⟩
  let e := canonicalUnitPlaneAlgEquiv25
  let E₀ := AlgebraicCurve.discreteValuationRingPlaceAlgEquiv ℚ
    (UnitPlanePointLocalRing25 u v hr) UnitPlaneFF25
  let E : UnitPlanePointLocalRing25 u v hr ≃+*
      (AlgebraicCurve.Place.mapAlgEquiv e p).toValuationSubring := E₀.toRingEquiv.trans
    (AlgebraicCurve.Place.mapValuationRingEquiv e p.toValuationSubring)
  obtain ⟨t, ht⟩ := hunit.map E.toMonoidHom
  have hcoe : ((t : (AlgebraicCurve.Place.mapAlgEquiv e p).toValuationSubring) :
      CanonicalFF25 ℚ) = e (algebraMap UnitPlaneRing UnitPlaneFF25 a) := by
    rw [ht]
    change e (algebraMap (UnitPlanePointLocalRing25 u v hr) UnitPlaneFF25
      (algebraMap UnitPlaneRing (UnitPlanePointLocalRing25 u v hr) a)) = _
    exact congrArg e (IsScalarTower.algebraMap_apply UnitPlaneRing
      (UnitPlanePointLocalRing25 u v hr) UnitPlaneFF25 a).symm
  have horder := (AlgebraicCurve.Place.mapAlgEquiv e p).ord_coe_unit t
  rw [hcoe] at horder
  exact horder

/-- Both plane-coordinate functions have order zero at a point with nonzero
first coordinate and nonzero second coordinate. -/
theorem _root_.solution
    (u v : ℚ) (hr : planeRelation u v = 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    (canonicalPointPlaceOfUnitPlane25 u v hr hu).ord canonicalFunctionU25 = 0 ∧
      (canonicalPointPlaceOfUnitPlane25 u v hr hu).ord canonicalFunctionV25 = 0 := by
  constructor
  · apply canonicalPointPlaceOfUnitPlane25_order_eq_zero u v hr hu unitPlaneU
    simpa [unitPlaneEvaluation25, unitPlaneU, AdjoinRoot.algebraMap_eq] using hu
  · apply canonicalPointPlaceOfUnitPlane25_order_eq_zero u v hr hu unitPlaneV
    simpa [unitPlaneEvaluation25, unitPlaneV] using hv

open MazurProof.RationalPointsN25CanonicalPoints

end N25
