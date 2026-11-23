-- Prove2me | solution 1 for GlobalTheory.periodCoordFst_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:05.430327+00:00
-- url     : https://prove2.me/submissions/8ef57f85-a901-4b80-abec-1d7b3aae6a49

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_im_mulVec_ofRealVec_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {τ : Matrix ι ι ℂ} (hτ : IsUnit (τ.map Complex.im).det)
    (u v : ι → ℝ) : periodCoordFst τ (τ *ᵥ ofRealVec u + ofRealVec v) = u := by
  unfold periodCoordFst
  rw [im_mulVec_ofRealVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hτ,
    Matrix.one_mulVec]
end GlobalTheory
