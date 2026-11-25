-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:27.215041+00:00
-- url     : https://prove2.me/submissions/bcb6d2e5-0ca7-4329-b4b9-789786a85fbb

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
variable [(W.baseChange k).IsElliptic] [(W.baseChange K).IsElliptic]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (p : (W.baseChange k).toAffine.Point) :
    affinePointEquiv W k p = ofAffinePoint W k p := rfl
end GlobalTheory.WeierstrassCurve
