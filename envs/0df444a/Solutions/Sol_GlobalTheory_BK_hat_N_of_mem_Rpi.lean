-- Prove2me | solution 1 for GlobalTheory.BK.hat_N_of_mem_Rpi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:01:07.648765+00:00
-- url     : https://prove2.me/submissions/411f5717-54df-4c89-b6be-6f16f549f43d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_toHat_derivative
import Theorems.Thm_GlobalTheory_BK_N_apply
import Theorems.Thm_GlobalTheory_BK_dHatE_algebraMap
import Theorems.Thm_GlobalTheory_BK_derivative_mem_R
import Theorems.Thm_GlobalTheory_BK_hat_coe_Rpi
import Theorems.Thm_GlobalTheory_BK_hat_mul


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
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
namespace GlobalTheory.BK
theorem _root_.solution {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) :
    hat O l e (N K f) = NHatE O K l e (hat O l e f) := by
  have hu : hat O l e (X : K⟦X⟧) = algebraMap _ _ (uhat O K l e) :=
    (hat_coe_Rpi l e (uIn _)).trans (congrArg _ (toHat_eq_ofAl l e rfl))
  rw [N_apply, hat_mul l e HasU.X_mem (le_away _ _ (derivative_mem_R l hf)), hu,
    hat_coe_Rpi l e ⟨f, hf⟩, hat_coe_Rpi l e ⟨_, derivative_mem_R l hf⟩, toHat_derivative l e ⟨f, hf⟩,
    NHatE, Derivation.smul_apply, dHatE_algebraMap, smul_eq_mul]
end GlobalTheory.BK
