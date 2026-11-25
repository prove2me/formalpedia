-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.ofAffinePoint_some
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:23.869092+00:00
-- url     : https://prove2.me/submissions/23272b4d-c6da-41f9-badf-2d5deb47939d

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
theorem _root_.solution {a b : k} (h : (W.baseChange k).toAffine.Nonsingular a b) :
    ofAffinePoint W k (.some a b h) = ptOver W ![a, b, 1] (isUnimodularSol_some h.left) := rfl
end GlobalTheory.WeierstrassCurve
