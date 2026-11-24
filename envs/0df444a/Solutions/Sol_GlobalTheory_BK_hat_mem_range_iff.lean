-- Prove2me | solution 1 for GlobalTheory.BK.hat_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:07.956579+00:00
-- url     : https://prove2.me/submissions/78093e3a-6369-40f7-8157-0c80659f4637

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_algebraMap_AhatE_injective
import Theorems.Thm_GlobalTheory_BK_hat_E_pow_mul
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_hat_coe_Rpi
import Theorems.Thm_P2M_GlobalTheory_BK_eval__toHat_eq_iff_7e88105c9732
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
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
namespace GlobalTheory.BK
theorem _root_.solution {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) :
    (∃ x : Ahat O K l e, algebraMap _ _ x = hat O l e f) ↔ f ∈ Rpi O K l e := by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun h => ⟨_, (hat_coe_Rpi l e ⟨f, h⟩).symm⟩⟩
  obtain ⟨n, hn⟩ := id hf
  have h1 : toHat O K l e ⟨_, hn⟩ = Ehat O K l e ^ n * x := algebraMap_AhatE_injective l e (by
    rw [← hat_coe_Rpi, map_mul, hx]
    exact hat_E_pow_mul l e n hf)
  have hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) =
      Ideal.Quotient.mk _ (EIn l e _) := AlgHom.commutes _ _
  obtain ⟨h, hh, H⟩ := (evalₐ_toHat_eq_iff l e n ⟨_, hn⟩ 0).1 (by
    rw [h1, map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul, map_zero])
  have H' : E K l e ^ n * f = E K l e ^ n * h := by simpa using H
  rwa [((isUnit_E l e).pow n).mul_left_cancel H']
end GlobalTheory.BK
