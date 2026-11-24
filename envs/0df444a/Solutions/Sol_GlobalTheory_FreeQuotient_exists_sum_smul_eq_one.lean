-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.exists_sum_smul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:28.93383+00:00
-- url     : https://prove2.me/submissions/dec0eab8-0ea6-40c3-8d32-ba92ec1548cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_exists_sum_sub_card_smul_mem
import Theorems.Thm_GlobalTheory_isIntegral_fixedSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
variable (G A)
namespace GlobalTheory.FreeQuotient
theorem _root_.solution
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P) :
    ∃ c : A, ∑ g : G, g • c = 1 := by
  let B := FixedPoints.subring A G
  haveI := isIntegral_fixedSubring A G
  have : LinearMap.range (ringTrace G B A) = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨P, hP, rfl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) Q
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
          exact bot_le)
    obtain ⟨s, hs⟩ := exists_sum_sub_card_smul_mem (G := G) P (1 : A) (by simp)
    rw [smul_eq_mul, Ideal.mul_top, smul_eq_mul, mul_one] at hs
    refine h P hP ((Submodule.sub_mem_iff_right _ (Ideal.sum_mem _ fun p _ ↦ ?_)).mp hs)
    refine P.mul_mem_left _ ?_
    rw [← algebraMap_ringTrace G B A]
    exact hle ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := LinearMap.range_eq_top.mp this 1
  exact ⟨c, by rw [← algebraMap_ringTrace G B A, hc, map_one]⟩
end GlobalTheory.FreeQuotient
