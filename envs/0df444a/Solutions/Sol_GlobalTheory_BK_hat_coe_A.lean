-- Prove2me | solution 1 for GlobalTheory.BK.hat_coe_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:08.585411+00:00
-- url     : https://prove2.me/submissions/ab47e91b-2c21-4dfa-9c30-6be2b05866a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_hat_coe_Rpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution (f : A O K) : hat O l e (f : K⟦X⟧) = algebraMap _ _ (ofA O K l e f) := by
  rw [show (f : K⟦X⟧) = (⟨f, A_le_Rpi l e f.2⟩ : Rpi O K l e) from rfl, hat_coe_Rpi]
  exact congrArg _ (toHat_eq_ofAl l e rfl)
end GlobalTheory.BK
