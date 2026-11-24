-- Prove2me | solution 1 for GlobalTheory.periodCoordSnd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:28:20.827866+00:00
-- url     : https://prove2.me/submissions/80953d11-8b1a-4d41-856f-1612e1064514

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_re_mulVec_ofRealVec_add
import Theorems.Thm_GlobalTheory_periodCoordFst_apply

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
    (u v : ι → ℝ) : periodCoordSnd τ (τ *ᵥ ofRealVec u + ofRealVec v) = v := by
  unfold periodCoordSnd
  rw [periodCoordFst_apply hτ, re_mulVec_ofRealVec_add]
  abel
end GlobalTheory
