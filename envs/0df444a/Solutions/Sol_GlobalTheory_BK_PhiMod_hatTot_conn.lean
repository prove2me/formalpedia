-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.hatTot_conn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:13.715951+00:00
-- url     : https://prove2.me/submissions/234a75fe-e41d-4d96-b544-1f29e67ba75e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_N_mem_RpiE
import Theorems.Thm_GlobalTheory_BK_hat_N
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_apply_eq
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_add
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_hat_of_mem
import Theorems.Thm_GlobalTheory_BK_mem_tot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



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
theorem _root_.solution (hN : ∀ j, P.conn (bas j) ∈ P.Mext (RpiE O K l e)) {v : Vec K a ι}
    (hv : v ∈ P.Mext (RpiE O K l e)) : P.hatTot (P.conn v) = P.connHat (P.hatTot v) := by
  ext τ i
  have h1 (j) : v τ j ∈ RpiE O K l e := mem_tot.1 hv τ j
  have h2 (j) : P.conn (bas j) τ i ∈ RpiE O K l e := mem_tot.1 (hN j) τ i
  have h3 : ∑ j, v τ j * P.conn (bas j) τ i =
      ((∑ j, ⟨_, h1 j⟩ * ⟨_, h2 j⟩ : RpiE O K l e) : K⟦X⟧) := by simp
  change hat O l e (P.conn v τ i) = NHatE O K l e (hat O l e _) + ∑ j, hat O l e _ * hat O l e _
  rw [conn_apply_eq, hat_add l e (N_mem_RpiE l e (h1 i))
    (sum_mem fun j _ => mul_mem (h1 j) (h2 j)), hat_N l e (h1 i), h3, hat_coe, map_sum]
  simp only [map_mul, hat_of_mem l e (h1 _), hat_of_mem l e (h2 _)]
end GlobalTheory.BK.PhiMod
