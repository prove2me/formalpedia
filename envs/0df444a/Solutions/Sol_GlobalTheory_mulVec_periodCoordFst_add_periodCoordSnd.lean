-- Prove2me | solution 1 for GlobalTheory.mulVec_periodCoordFst_add_periodCoordSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:30.965953+00:00
-- url     : https://prove2.me/submissions/fda9b189-03aa-4d3b-9704-f0744adf94ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_im_mulVec_ofRealVec_add
import Theorems.Thm_GlobalTheory_re_mulVec_ofRealVec_add

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
theorem _root_.solution {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (w : ι → ℂ) :
    τ *ᵥ ofRealVec (periodCoordFst τ w) + ofRealVec (periodCoordSnd τ w) = w := by
  ext i
  apply Complex.ext
  · have h := congrFun
      (re_mulVec_ofRealVec_add τ (periodCoordFst τ w) (periodCoordSnd τ w)) i
    rw [h]
    simp [periodCoordSnd]
  · have h := congrFun
      (im_mulVec_ofRealVec_add τ (periodCoordFst τ w) (periodCoordSnd τ w)) i
    rw [h]
    unfold periodCoordFst
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hτ, Matrix.one_mulVec]
end GlobalTheory
