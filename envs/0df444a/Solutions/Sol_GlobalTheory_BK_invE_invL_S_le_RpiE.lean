-- Prove2me | solution 1 for GlobalTheory.BK.invE_invL_S_le_RpiE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:23.046494+00:00
-- url     : https://prove2.me/submissions/f113bc54-213f-4269-ae4f-b808e6ab31bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_invE_le_RpiE


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
theorem _root_.solution : invE l e (invL l (S O K e)) ≤ RpiE O K l e :=
  invE_le_RpiE l e (invL_S_le_Rpi l e)
end GlobalTheory.BK
