-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_ptOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:27.915067+00:00
-- url     : https://prove2.me/submissions/044d22af-11c4-4f3e-835c-5cacab2e31de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffine
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


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
variable (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K]
variable [(W.baseChange k).IsElliptic] [(W.baseChange K).IsElliptic]
variable {k}
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (P : Fin 3 → k) (h : IsUnimodularSol (W.baseChange k) P) :
    (affinePointEquiv W k).symm (ptOver W P h) =
      WeierstrassCurve.Projective.Point.toAffine (W.baseChange k).toProjective P :=
  (Equiv.symm_apply_eq _).mpr (ofAffinePoint_toAffine W h.nonsingular).symm
end GlobalTheory.WeierstrassCurve
