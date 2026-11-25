-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:30:50.822475+00:00
-- url     : https://prove2.me/submissions/fdc6f34f-426b-4689-8dee-0078a61ac17c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra

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
variable {k}
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (p : (W.baseChange k).toProjective.Point) :
    ofAffinePoint W k p.toAffineLift = ofProjectivePoint W k p := by
  classical
  exact congrArg (ofProjectivePoint W k)
    ((WeierstrassCurve.Projective.Point.toAffineAddEquiv _).symm_apply_apply p)
end GlobalTheory.WeierstrassCurve
