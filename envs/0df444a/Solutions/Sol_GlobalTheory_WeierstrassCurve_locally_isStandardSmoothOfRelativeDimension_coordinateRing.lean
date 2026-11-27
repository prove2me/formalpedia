-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.locally_isStandardSmoothOfRelativeDimension_coordinateRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:31.419693+00:00
-- url     : https://prove2.me/submissions/3d3d8a39-d253-4682-a1f2-49b8b85de335

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open MvPolynomial
variable {i j : Fin 3} (hij : j ≠ i)
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution [W.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R W.toAffine.CoordinateRing) := by
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)
    (φ := CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing))).1 ?_
  rw [← chartZ_toSpec]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
end GlobalTheory.WeierstrassCurve
