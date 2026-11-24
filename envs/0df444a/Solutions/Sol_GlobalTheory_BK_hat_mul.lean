-- Prove2me | solution 1 for GlobalTheory.BK.hat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:09.173802+00:00
-- url     : https://prove2.me/submissions/1d5e48c2-e445-429e-80cc-37743ef985f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_hat_of_mem
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.hat_coe

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
variable {O K}
namespace GlobalTheory.BK
theorem _root_.solution {f g : K⟦X⟧} (hf : f ∈ RpiE O K l e) (hg : g ∈ RpiE O K l e) :
    hat O l e (f * g) = hat O l e f * hat O l e g := by
  rw [hat_of_mem l e hf, hat_of_mem l e hg, ← map_mul, ← hat_coe]
  rfl
end GlobalTheory.BK
