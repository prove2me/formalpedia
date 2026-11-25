-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.smul_hatTot_mem_Mhat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:39:25.988448+00:00
-- url     : https://prove2.me/submissions/724f1bbb-99b2-4d7b-b913-2b8db58158b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_hat_E_pow_mul
import Theorems.Thm_GlobalTheory_BK_mem_divE
import Theorems.Thm_GlobalTheory_BK_PhiMod_hatTot_mem_Mhat_iff
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_tot_mem_Mext
import Theorems.Thm_GlobalTheory_BK_Raises_pow_mem
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
theorem _root_.solution (η : ℕ) {v : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e)) :
    Ehat O K l e ^ η • P.hatTot v ∈ P.Mhat ↔ v ∈ divE l e η P.Man := by
  have : Ehat O K l e ^ η • P.hatTot v = P.hatTot (E K l e ^ η • v) := funext fun τ => funext fun i =>
    (Algebra.smul_def _ _).trans (hat_E_pow_mul l e η (mem_tot.1 hv τ i)).symm
  rw [this, mem_divE]
  exact P.hatTot_mem_Mhat_iff
    (P.smul_tot_mem_Mext (f := fun _ => E K l e ^ η) (fun _ => pow_mem (E_mem l e _) η) hv)
end GlobalTheory.BK.PhiMod
