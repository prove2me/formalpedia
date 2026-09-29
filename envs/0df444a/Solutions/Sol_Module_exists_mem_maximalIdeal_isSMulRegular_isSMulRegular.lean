-- Prove2me | solution 1 for Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9c31dd24-deca-5107-9dcd-0f14a7355256

import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular

theorem solution {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (N₁ N₂ : Type*) [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂] (h₁ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₁) (h₂ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₂) :
    ∃ z ∈ IsLocalRing.maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  by_contra hcon
  have hsub : (IsLocalRing.maximalIdeal R : Set R) ⊆
      ⋃ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂ : Set (Ideal R)), (p : Set R) := by
    intro z hz
    rw [Set.biUnion_union]
    by_cases hreg : IsSMulRegular N₁ z
    · refine Set.mem_union_right _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₂]
      exact fun hreg2 => hcon ⟨z, hz, hreg, hreg2⟩
    · refine Set.mem_union_left _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₁]
      exact hreg
  have hfin : (associatedPrimes R N₁ ∪ associatedPrimes R N₂).Finite :=
    (associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)
  have hprime : ∀ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂),
      p ≠ (⊥ : Ideal R) → p ≠ (⊥ : Ideal R) → (id p).IsPrime := by
    rintro p (hp | hp) - -
    · exact hp.isPrime
    · exact hp.isPrime
  obtain ⟨p, hpmem, hple⟩ := (Ideal.subset_union_prime_finite hfin (f := id)
    (I := IsLocalRing.maximalIdeal R) ⊥ ⊥ hprime).mp (by simpa using hsub)
  have hpprime : p.IsPrime := by
    rcases hpmem with hp | hp
    · exact hp.isPrime
    · exact hp.isPrime
  have hpeq : p = IsLocalRing.maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hpprime.ne_top) hple
  rw [hpeq] at hpmem
  rcases hpmem with hp | hp
  · exact h₁ hp
  · exact h₂ hp

end S_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular
end P2MW
export P2MW.S_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular (solution)
