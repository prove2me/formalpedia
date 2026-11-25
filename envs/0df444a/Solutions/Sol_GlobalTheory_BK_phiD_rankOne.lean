-- Prove2me | solution 1 for GlobalTheory.BK.phiD_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:32:00.203884+00:00
-- url     : https://prove2.me/submissions/6994bcd1-99da-4e7c-963a-139e9d9be738

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_PhiMod_phiD_apply
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_mx_rankOne
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
theorem _root_.solution {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = n)
    (d : (rankOne O K l e j).D) : (rankOne O K l e j).phiD d τ () = (l : K) ^ n * d (τ - 1) () := by
  simp [PhiMod.phiD_apply, PhiMod.mx0, Matrix.mulVec, dotProduct, mx_rankOne h, constantCoeff_E]
end GlobalTheory.BK
