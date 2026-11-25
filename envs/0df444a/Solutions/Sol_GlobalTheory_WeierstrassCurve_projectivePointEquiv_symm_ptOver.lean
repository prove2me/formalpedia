-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_ptOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:43.169475+00:00
-- url     : https://prove2.me/submissions/9b1dee16-1d21-4619-a895-97ed93515734

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
variable [(W.baseChange k).IsElliptic] [(W.baseChange K).IsElliptic]
variable {k}
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (P : Fin 3 → k)
    (h : IsUnimodularSol (W.baseChange k) P) :
    (projectivePointEquiv W k).symm (ptOver W P h) =
      ⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr h.nonsingular⟩ :=
  (Equiv.symm_apply_eq _).mpr rfl
end GlobalTheory.WeierstrassCurve
