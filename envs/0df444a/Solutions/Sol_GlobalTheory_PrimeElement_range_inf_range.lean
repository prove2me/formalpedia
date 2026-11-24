-- Prove2me | solution 1 for GlobalTheory.PrimeElement.range_inf_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:44:40.412908+00:00
-- url     : https://prove2.me/submissions/94e44268-4010-44ec-b8fe-1dd6b50f56dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Theorems.Thm_GlobalTheory_PrimeElement_mem_primeCompl_span
import Theorems.Thm_GlobalTheory_PrimeElement_exists_eq_of_pow_mul_of_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
variable [(Ideal.span {π}).IsPrime]
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  (K : Type*) [CommRing K] [IsDomain K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K]
namespace GlobalTheory.PrimeElement
theorem _root_.solution (hπ : π ≠ 0) :
    (algebraMap A K).range ⊓ (algebraMap S K).range = (algebraMap R K).range := by
  have hp : Prime π := (Ideal.span_singleton_prime hπ).1 inferInstance
  refine le_antisymm ?_ ?_
  · rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h₁⟩ := IsLocalization.surj (Submonoid.powers π) y
    obtain ⟨⟨c, ⟨b, hb⟩⟩, h₂⟩ := IsLocalization.surj (Ideal.span {π}).primeCompl z
    refine exists_eq_of_pow_mul_of_mul hp (n := n) (a := a) (c := c) ?_
      (mem_primeCompl_span.1 hb) ?_
    · rw [IsScalarTower.algebraMap_apply R A K, IsScalarTower.algebraMap_apply R A K a, ← h₁,
        map_mul, hy, mul_comm]
    · rw [IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K c, ← h₂,
        map_mul, hz, mul_comm]
  · rintro _ ⟨r, rfl⟩
    exact ⟨⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A K r).symm⟩,
      ⟨algebraMap R S r, (IsScalarTower.algebraMap_apply R S K r).symm⟩⟩
end GlobalTheory.PrimeElement
