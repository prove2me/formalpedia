-- Prove2me | solution 1 for GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:29.74186+00:00
-- url     : https://prove2.me/submissions/54ea83e4-f02b-4ba1-930c-476533cbb834

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemRangeOfForallAlgHomEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlat
import Theorems.Thm_GlobalTheory_SymDesc_exists_sub_mem_of_under_eq_bot
import Theorems.Thm_GlobalTheory_SymDesc_eq_of_sub_mem

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
theorem _root_.solution : ∀ (R R₁ : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ →
    Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) →
    ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  intro R R₁ _ _ _ _ _ _ hfin hff s hs
  haveI := hfin
  haveI := hff
  haveI : Algebra.IsIntegral R R₁ := Algebra.IsIntegral.of_finite R R₁
  have hinj : Function.Injective (algebraMap R R₁) := FaithfulSMul.algebraMap_injective R R₁
  have hker : Ideal.comap (algebraMap R R₁) (⊥ : Ideal R₁) ≤ ⊥ := by
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    exact hinj (by rw [hr, map_zero])
  obtain ⟨Q₀, -, hQ₀, hQ₀b⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal R) ⊥ hker
  haveI := hQ₀
  obtain ⟨e, he⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q₀ hQ₀b
  refine ⟨e, fun K _ i₁ => ?_⟩
  let P := RingHom.ker i₁
  haveI : P.IsPrime := RingHom.ker_isPrime i₁
  haveI : P.LiesOver (P.under R) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQo⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R)) (q := P.under R) P bot_le
  have hQb : Q.comap (algebraMap R R₁) = ⊥ := hQo.over.symm
  obtain ⟨e₁, he₁⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q hQb
  have hee := SymDesc.eq_of_sub_mem s hs Q₀ Q hQ₀b hQb e e₁ he he₁
  subst hee
  have hm : s - algebraMap R R₁ e ∈ P := hQP he₁
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  exact hm
end GlobalTheory
