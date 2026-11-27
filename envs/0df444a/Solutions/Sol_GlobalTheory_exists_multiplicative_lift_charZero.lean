-- Prove2me | solution 1 for GlobalTheory.exists_multiplicative_lift_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:26.197041+00:00
-- url     : https://prove2.me/submissions/87791cb2-71e5-4f28-9276-4d4674803269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsMultiplicativeLiftCharZero
import Theorems.Thm_GlobalTheory_charZero_wittVector_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K], ∃ (K' : Type) (_ : Field K') (_ : CharZero K') (τ : K →*₀ K'), Function.Injective τ ∧ ∀ (ι : Type) (s : Finset ι) (f : ι → K), ∑ i ∈ s, τ (f i) = 0 → ∑ i ∈ s, f i = 0 := by
  intro K _
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with h | h
  · haveI : Fact p.Prime := ⟨h⟩
    haveI := charZero_wittVector_of_field p K
    have hinj := IsFractionRing.injective (WittVector p K) (FractionRing (WittVector p K))
    haveI : CharZero (FractionRing (WittVector p K)) := charZero_of_injective_algebraMap hinj
    let τ : K →*₀ FractionRing (WittVector p K) :=
      { toFun := fun a => algebraMap (WittVector p K) _ (WittVector.teichmuller p a)
        map_zero' := by simp
        map_one' := by simp
        map_mul' := by intro a b; simp }
    have hτ : ∀ a, τ a = algebraMap (WittVector p K) _ (WittVector.teichmuller p a) := fun _ => rfl
    have hc : ∀ a : K, (WittVector.constantCoeff : WittVector p K →+* K)
        (WittVector.teichmuller p a) = a := fun a => by
      simp [WittVector.constantCoeff_apply]
    refine ⟨FractionRing (WittVector p K), inferInstance, inferInstance, τ, ?_, ?_⟩
    · intro a b hab
      rw [hτ, hτ] at hab
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (hinj hab)
      rwa [hc, hc] at this
    · intro ι s f hf
      simp only [hτ] at hf
      rw [← map_sum, ← map_zero (algebraMap (WittVector p K) (FractionRing (WittVector p K)))] at hf
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (hinj hf)
      rw [map_sum, map_zero] at this
      simpa only [hc] using this
  · subst h
    haveI : CharZero K := CharP.charP_to_charZero K
    exact ⟨K, inferInstance, inferInstance, MonoidWithZeroHom.id K, fun _ _ h => h, fun _ _ _ h => h⟩
end GlobalTheory
