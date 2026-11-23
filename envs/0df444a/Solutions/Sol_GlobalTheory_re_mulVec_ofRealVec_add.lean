-- Prove2me | solution 1 for GlobalTheory.re_mulVec_ofRealVec_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:08.455599+00:00
-- url     : https://prove2.me/submissions/8877a88f-b232-4ca2-a695-15c22b2fefa4

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
    (fun i => ((τ *ᵥ ofRealVec u + ofRealVec v) i).re) = τ.map Complex.re *ᵥ u + v := by
  ext i
  simp [ofRealVec, Matrix.mulVec, dotProduct, Complex.re_sum]
end GlobalTheory
