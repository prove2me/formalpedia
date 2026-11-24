-- Prove2me | solution 1 for GlobalTheory.mem_associatedPrimes_iff_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:20:02.33069+00:00
-- url     : https://prove2.me/submissions/a577cdc4-28d6-4b63-9e5b-39c71cfdd239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_mem_minimalPrimes_span_singleton_of_height_eq_one
import Theorems.Thm_GlobalTheory_height_eq_one_of_mem_associatedPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution {a : A} (ha : a ≠ 0) {p : Ideal A} :
    p ∈ associatedPrimes A (A ⧸ Ideal.span {a}) ↔ p.IsPrime ∧ p.height = 1 ∧ a ∈ p := by
  have hann : Module.annihilator A (A ⧸ Ideal.span {a}) = Ideal.span {a} :=
    Ideal.annihilator_quotient
  constructor
  · intro hp
    refine ⟨hp.1, height_eq_one_of_mem_associatedPrimes ha hp, ?_⟩
    have := IsAssociatedPrime.annihilator_le hp
    rw [Submodule.annihilator_top, hann] at this
    exact this (Ideal.mem_span_singleton_self a)
  · rintro ⟨_, hp, hap⟩
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [hann]
    exact mem_minimalPrimes_span_singleton_of_height_eq_one hp ha hap
end GlobalTheory
