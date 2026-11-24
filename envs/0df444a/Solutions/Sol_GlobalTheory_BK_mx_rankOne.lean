-- Prove2me | solution 1 for GlobalTheory.BK.mx_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:53:53.529425+00:00
-- url     : https://prove2.me/submissions/fea7821f-16ce-47ed-924a-9f39c4b1c27f

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
theorem _root_.solution {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = n) :
    (rankOne O K l e j).mx τ () () = E K l e ^ n := by
  simp [PhiMod.mx, rankOne, h, Matrix.diagonal_pow]
end GlobalTheory.BK
