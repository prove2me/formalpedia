-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.locally_isStandardSmoothOfRelativeDimension_originRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:34.372791+00:00
-- url     : https://prove2.me/submissions/d4e04282-b1b4-4909-a63b-b8d575cb3fa7

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
      (algebraMap R (OriginRing W)) := by
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)
    (φ := CommRingCat.ofHom (algebraMap R (OriginRing W)))).1 ?_
  rw [← chartY_toSpec]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
end GlobalTheory.WeierstrassCurve
