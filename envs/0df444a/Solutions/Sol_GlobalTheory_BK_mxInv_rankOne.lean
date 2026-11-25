-- Prove2me | solution 1 for GlobalTheory.BK.mxInv_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:48:13.19103+00:00
-- url     : https://prove2.me/submissions/57136f9c-7ca6-417a-a654-d0ca4c0592d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.hat_coe
attribute [local simp] GlobalTheory.BK.coe_Eunit

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {O K l e a}
namespace GlobalTheory.BK
theorem _root_.solution {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = -n) :
    (rankOne O K l e j).mxInv τ () () = E K l e ^ n := by
  simp [PhiMod.mxInv, rankOne, h, ← map_inv, Matrix.diagonal_pow]
end GlobalTheory.BK
