-- Prove2me | solution 1 for N25.canonicalProjectiveCurveToSpec25_isProper
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:50.861866+00:00
-- url     : https://prove2.me/submissions/049ee4a9-f0a9-483b-bf84-02a2a1ab32a9

import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! Properness of the literal canonical projective model over its selected coefficient field. -/
noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory

variable (K : Type u) [Field K]

/-- Four degree-one coordinates generate the homogeneous coordinate algebra. -/
instance canonicalConeRing25_finiteType_s1a01bc :
    Algebra.FiniteType (canonicalConePiece25 K 0) (CanonicalConeRing25 K) := by
  classical
  refine ⟨⟨Finset.univ.image (canonicalConeCoordinate25 K), ?_⟩⟩
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    using canonicalConeCoordinates25_adjoin K

/-- The structure map of the literal canonical Proj is proper over every coefficient field. -/
theorem _root_.solution : IsProper (canonicalProjectiveCurveToSpec25 K) := by
  haveI : IsIso (CommRingCat.ofHom (algebraMap K (canonicalConePiece25 K 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (canonicalConePieceZero25_algebraMap_bijective K)
  unfold canonicalProjectiveCurveToSpec25
  infer_instance

end N25
