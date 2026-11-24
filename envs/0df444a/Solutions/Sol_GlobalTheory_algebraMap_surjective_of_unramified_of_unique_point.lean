-- Prove2me | solution 1 for GlobalTheory.algebraMap_surjective_of_unramified_of_unique_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:16.697645+00:00
-- url     : https://prove2.me/submissions/268ffa8d-511a-47ad-9ce1-fa7c35f0bc3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint

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
namespace GlobalTheory
theorem _root_.solution (K A : Type) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.FormallyUnramified K A]
    (φ : A →ₐ[K] K) (hφ : ∀ ψ : A →ₐ[K] K, ψ = φ) : Function.Surjective (algebraMap K A) := by
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  have hker : ∀ a : A, φ a = 0 → a = 0 := by
    intro a ha
    apply IsNilpotent.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hb : Function.Bijective (algebraMap K (A ⧸ J)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : K ≃ₐ[K] (A ⧸ J) := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ J)) hb
    have h := hφ ((e.symm : (A ⧸ J) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K J))
    rw [← h] at ha
    have h2 : e.symm (Ideal.Quotient.mk J a) = 0 := ha
    rw [map_eq_zero_iff _ e.symm.injective] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  intro a
  refine ⟨φ a, ?_⟩
  rw [← sub_eq_zero]
  apply hker
  simp
end GlobalTheory
