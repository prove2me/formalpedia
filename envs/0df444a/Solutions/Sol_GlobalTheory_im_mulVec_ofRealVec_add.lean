-- Prove2me | solution 1 for GlobalTheory.im_mulVec_ofRealVec_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:08.295134+00:00
-- url     : https://prove2.me/submissions/aeb88b7e-40f9-42c6-863b-6d3c912a8dcd

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice

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
omit [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec u + ofRealVec v) i).im) = τ.map Complex.im *ᵥ u := by
  ext i
  simp [ofRealVec, Matrix.mulVec, dotProduct, Complex.im_sum]
end GlobalTheory
