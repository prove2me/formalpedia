-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.exists_sub_hatTot_mem_Mhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:43.069501+00:00
-- url     : https://prove2.me/submissions/62d19ac8-b13f-4e52-88ad-bfa7cf547aaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_hat_E_pow_mul
import Theorems.Thm_GlobalTheory_BK_exists_eq_algebraMap_add_pow_mul
import Theorems.Thm_GlobalTheory_BK_E_pow_mul_Ezpow_neg
import Theorems.Thm_GlobalTheory_BK_PhiMod_mem_Mhat
import Theorems.Thm_GlobalTheory_BK_Rot_invL
import Theorems.Thm_GlobalTheory_BK_hat_coe_Rpi
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
theorem _root_.solution (η : ℕ) {w : ZMod a → ι → AhatE O K l e}
    (hw : Ehat O K l e ^ η • w ∈ P.Mhat) :
    ∃ v ∈ divE l e η (P.Mext (invL l (A O K))), w - P.hatTot v ∈ P.Mhat := by
  choose x hx using P.mem_Mhat.1 hw
  choose g x' hg using fun τ i =>
    exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) η (x τ i)
  have hE (τ i) : E K l e ^ η * (Ezpow K l e (-η) * g τ i) = g τ i := by
    rw [← mul_assoc, E_pow_mul_Ezpow_neg, one_mul]
  refine ⟨fun τ i => Ezpow K l e (-η) * g τ i, mem_tot.2 fun τ i => ?_,
    P.mem_Mhat.2 fun τ i => ⟨x' τ i, ?_⟩⟩
  · change E K l e ^ η * (Ezpow K l e (-η) * g τ i) ∈ invL l (A O K)
    rw [hE]
    exact (g τ i).2
  · have hg' := invL_A_le_Rpi l e (g τ i).2
    have h0 : Ezpow K l e (-η) * (g τ i : K⟦X⟧) ∈ RpiE O K l e := ⟨η, by rw [coe_EIn, hE]; exact hg'⟩
    have h1 := hat_E_pow_mul l e η h0
    rw [hE, hat_coe_Rpi l e ⟨_, hg'⟩, toHat_eq_ofAl l e (g := g τ i) rfl] at h1
    have h2 : algebraMap _ _ (x τ i) = algebraMap _ _ (Ehat O K l e ^ η) * w τ i :=
      (hx τ i).trans (Algebra.smul_def (Ehat O K l e ^ η) (w τ i))
    have h3 : x τ i = ofAl O K l e (g τ i) + Ehat O K l e ^ η * x' τ i := hg τ i
    rw [h3, map_add, map_mul, h1, add_comm, ← eq_sub_iff_add_eq, ← mul_sub, map_pow] at h2
    exact ((IsLocalization.Away.algebraMap_isUnit (Ehat O K l e)).pow η).mul_left_cancel h2
end GlobalTheory.BK.PhiMod
