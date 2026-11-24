-- Prove2me | solution 1 for GlobalTheory.intVec_eq_zero_of_period_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:21.649979+00:00
-- url     : https://prove2.me/submissions/8cfdd2f8-a85b-45de-969a-8607359df613

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_intVec_eq_zero_of_periodCoord_lt_one
import Theorems.Thm_GlobalTheory_periodCoordFst_zero
import Theorems.Thm_GlobalTheory_periodCoordSnd_zero

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
    (hτ : IsUnit (τ.map Complex.im).det) (n n' : ι → ℤ)
    (h : τ *ᵥ ofIntVec n + ofIntVec n' = 0) : n = 0 ∧ n' = 0 := by
  apply intVec_eq_zero_of_periodCoord_lt_one hτ n n'
  · intro i; simp [h, periodCoordFst_zero]
  · intro i; simp [h, periodCoordSnd_zero]
end GlobalTheory
