-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.ofAffinePoint_map_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:34.260198+00:00
-- url     : https://prove2.me/submissions/d4d01d5e-b9c8-4bc5-a133-bf800e7981af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_pt_congr
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


attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K]
variable {k K}
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution [DecidableEq k] [DecidableEq K] {S : Type*} [CommRing S]
    [Algebra R S] [Algebra S k] [IsScalarTower R S k] [Algebra S K] [IsScalarTower R S K]
    (f : k →ₐ[S] K) (p : (W.baseChange k).toAffine.Point) :
    (ofAffinePoint W K (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f p)).left =
      Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (ofAffinePoint W k p).left := by
  rcases p with _ | ⟨a, b, h⟩
  · refine Eq.trans ?_ (SpecMap_pt W ![0, 1, 0] (isUnimodularSol_zero _) (f.restrictScalars R)).symm
    exact pt_congr W ![0, 1, 0] (isUnimodularSol_zero _) (by ext i; fin_cases i <;> simp) _
  · refine Eq.trans ?_
      (SpecMap_pt W ![a, b, 1] (isUnimodularSol_some h.left) (f.restrictScalars R)).symm
    exact pt_congr W ![f a, f b, 1] (isUnimodularSol_some
      ((W.toAffine.baseChange_nonsingular f.injective ..).mpr h).left)
      (by ext i; fin_cases i <;> simp) _
end GlobalTheory.WeierstrassCurve
