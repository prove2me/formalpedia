-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.ofAffinePoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:48.94498+00:00
-- url     : https://prove2.me/submissions/a3b6bfdd-b67e-4783-a0a7-21074dd82392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
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
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution : Function.Injective (ofAffinePoint W k) := by
  classical
  exact (ofProjectivePoint_injective W k).comp
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.baseChange k).toProjective).symm.injective
end GlobalTheory.WeierstrassCurve
