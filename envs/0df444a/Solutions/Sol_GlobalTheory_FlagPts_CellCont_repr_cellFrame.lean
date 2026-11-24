-- Prove2me | solution 1 for GlobalTheory.FlagPts.CellCont.repr_cellFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:15.901074+00:00
-- url     : https://prove2.me/submissions/ee7aaeb2-4da6-4b4e-8753-b60403015fdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace GlobalTheory.FlagPts
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.CellCont
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
namespace GlobalTheory.FlagPts.CellCont
theorem _root_.solution (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) (v : V i) :
    (cellFrame b u i).repr v = (uniMat u i).adjugate.mulVec ((b i).repr v) := by
  have hu : IsUnit (uniMat u i).det := by rw [det_uniMat]; exact isUnit_one
  have hM : (uniMat u i)⁻¹ = (uniMat u i).adjugate := by
    rw [Matrix.inv_def, det_uniMat]; simp
  rw [← hM]
  have he : (Matrix.toLinearEquiv (b i) (uniMat u i) hu).symm v =
      Matrix.toLin (b i) (b i) (uniMat u i)⁻¹ v := by
    rw [LinearEquiv.symm_apply_eq, Matrix.toLinearEquiv_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul,
      Matrix.mul_nonsing_inv _ hu, Matrix.toLin_one]
    rfl
  simp only [cellFrame, Basis.map_repr, LinearEquiv.trans_apply]
  rw [he, ← LinearMap.toMatrix_mulVec_repr (b i) (b i), LinearMap.toMatrix_toLin]
end GlobalTheory.FlagPts.CellCont
