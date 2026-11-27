-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.ofAffinePoint_of_represents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:52.324465+00:00
-- url     : https://prove2.me/submissions/5f27a261-f658-4204-bd28-9c3130c12eb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffine

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
theorem _root_.solution {P : Fin 3 → k} {p : (W.baseChange k).toAffine.Point}
    (h : AddLaw.Represents (W.baseChange k).toProjective P p) :
    ofAffinePoint W k p = ptOver W P (.of_nonsingular h.left) :=
  h.right ▸ ofAffinePoint_toAffine W h.left
end GlobalTheory.WeierstrassCurve
