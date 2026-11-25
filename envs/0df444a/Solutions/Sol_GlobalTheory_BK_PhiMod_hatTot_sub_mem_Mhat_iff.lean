-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.hatTot_sub_mem_Mhat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:28:48.803907+00:00
-- url     : https://prove2.me/submissions/88eb26c1-e919-49df-8029-0e366cde1eed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_hat_sub
import Theorems.Thm_GlobalTheory_BK_PhiMod_hatTot_mem_Mhat_iff
import Theorems.Thm_GlobalTheory_BK_mem_tot


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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
variable [NormedAlgebra ℚ_[l] K] [NeZero e]
variable [CompleteSpace K]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {v w : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e))
    (hw : w ∈ P.Mext (RpiE O K l e)) : P.hatTot v - P.hatTot w ∈ P.Mhat ↔ P.cls v = P.cls w := by
  have : P.hatTot v - P.hatTot w = P.hatTot (v - w) := funext fun τ => funext fun i =>
    (hat_sub l e (mem_tot.1 hv τ i) (mem_tot.1 hw τ i)).symm
  rw [this, P.hatTot_mem_Mhat_iff (sub_mem hv hw)]
  exact (Submodule.Quotient.eq _).symm
end GlobalTheory.BK.PhiMod
