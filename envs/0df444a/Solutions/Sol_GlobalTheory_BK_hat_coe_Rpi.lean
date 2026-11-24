-- Prove2me | solution 1 for GlobalTheory.BK.hat_coe_Rpi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:05:02.671801+00:00
-- url     : https://prove2.me/submissions/98932ccc-5388-4f4e-92e2-f8c40d63c557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_hat_of_mem
import Theorems.Thm_GlobalTheory_BK_toHatE_eq


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
theorem _root_.solution (f : Rpi O K l e) :
    hat O l e (f : K⟦X⟧) = algebraMap _ _ (toHat O K l e f) := by
  rw [hat_of_mem l e (le_away _ _ f.2)]
  exact toHatE_eq l e rfl
end GlobalTheory.BK
