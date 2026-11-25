-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:37.131839+00:00
-- url     : https://prove2.me/submissions/75967926-3ca2-4655-a08b-25dc18e4c886

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ


attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift

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
theorem _root_.solution {P : Fin 3 → k} (h : (W.baseChange k).toProjective.Nonsingular P) :
    ofAffinePoint W k (WeierstrassCurve.Projective.Point.toAffine (W.baseChange k).toProjective P) =
      ptOver W P (.of_nonsingular h) :=
  ofAffinePoint_toAffineLift W ⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr h⟩
end GlobalTheory.WeierstrassCurve
