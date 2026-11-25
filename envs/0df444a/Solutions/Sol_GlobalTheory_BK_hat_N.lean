-- Prove2me | solution 1 for GlobalTheory.BK.hat_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:41.8636+00:00
-- url     : https://prove2.me/submissions/ed23ee0a-e31c-4c8c-bb8f-ff5aa5e4a3e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_hat_E_pow_mul
import Theorems.Thm_GlobalTheory_BK_N_mem_RpiE
import Theorems.Thm_GlobalTheory_BK_hat_N_of_mem_Rpi
import Theorems.Thm_GlobalTheory_BK_Raises_pow_mem
import Theorems.Thm_GlobalTheory_BK_hat_add
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_hat_mul
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
namespace GlobalTheory.BK
theorem _root_.solution {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) :
    hat O l e (N K f) = NHatE O K l e (hat O l e f) := by
  obtain ⟨n, hn⟩ := id hf
  have hE : E K l e ^ n ∈ Rpi O K l e := pow_mem (E_mem l e _) n
  have hE' : E K l e ^ n ∈ RpiE O K l e := le_away _ _ hE
  have h1 := hat_N_of_mem_Rpi l e hn
  rw [coe_EIn, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    hat_add l e (mul_mem hE' (N_mem_RpiE l e hf)) (mul_mem hf (N_mem_RpiE l e hE')),
    hat_mul l e hf (N_mem_RpiE l e hE'), hat_N_of_mem_Rpi l e hE, hat_mul l e hE' hf,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_left_inj, hat_E_pow_mul l e n (N_mem_RpiE l e hf),
    ← mul_one (E K l e ^ n), hat_E_pow_mul l e n (one_mem _),
    show hat O l e (1 : K⟦X⟧) = 1 from (hat_coe l e 1).trans (map_one _), mul_one, map_pow] at h1
  exact ((IsLocalization.Away.algebraMap_isUnit (Ehat O K l e)).pow n).mul_left_cancel h1
end GlobalTheory.BK
