-- Prove2me | solution 1 for GlobalTheory.ChartRing.algHom_ext_of_isHausdorff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:09.935819+00:00
-- url     : https://prove2.me/submissions/ea0e098b-d5e4-4f9a-b0f9-55112816375a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_pow_dvd_sub_aeval_trunc
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ChartRing.evalAdic_X
attribute [local simp] GlobalTheory.ChartRing.evalAdic_C

set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)
namespace GlobalTheory.ChartRing
theorem _root_.solution (J : Ideal S) [IsHausdorff J S] {φ ψ : A⟦X⟧ →ₐ[A] S}
    (hφ : φ X ∈ J) (h : φ X = ψ X) : φ = ψ := by
  refine AlgHom.ext fun f => ?_
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero]
  have h1 := pow_dvd_sub_aeval_trunc φ n f
  have h2 := pow_dvd_sub_aeval_trunc ψ n f
  rw [← h] at h2
  have h3 : φ X ^ n ∣ φ f - ψ f := by simpa using dvd_sub h1 h2
  simpa using Ideal.mem_of_dvd _ h3 (Ideal.pow_mem_pow hφ n)
end GlobalTheory.ChartRing
