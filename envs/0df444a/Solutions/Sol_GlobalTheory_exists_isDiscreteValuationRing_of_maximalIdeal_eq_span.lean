-- Prove2me | solution 1 for GlobalTheory.exists_isDiscreteValuationRing_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:20.373457+00:00
-- url     : https://prove2.me/submissions/b8c6b0b1-19a9-4847-b1f2-da0334657b45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution {B : Type*} [CommRing B]
    [IsLocalRing B] {t : B} (ht : t ∈ nonZeroDivisors B) (hm : maximalIdeal B = Ideal.span {t})
    (hs : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥) :
    ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  classical
  have key : ∀ x : B, x ≠ 0 → ∃ (n : ℕ) (u : Bˣ), t ^ n * u = x := by
    intro x hx
    have h : ∃ n : ℕ, ¬ t ^ n ∣ x := by
      by_contra hc
      push Not at hc
      apply hx
      rw [← Ideal.mem_bot, ← hs, Ideal.mem_iInf]
      intro n
      rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hc n
    have h₀ : Nat.find h ≠ 0 := fun h₀ => Nat.find_spec h (by simp [h₀])
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h₀
    obtain ⟨u, rfl⟩ := not_not.mp (Nat.find_min h (hn ▸ n.lt_succ_self))
    have hu : IsUnit u := by
      by_contra hu
      have h₁ : u ∈ maximalIdeal B := hu
      rw [hm, Ideal.mem_span_singleton] at h₁
      exact Nat.find_spec h (by rw [hn, pow_succ]; exact mul_dvd_mul_left _ h₁)
    exact ⟨n, hu.unit, rfl⟩
  have hreg : ∀ x : B, x ≠ 0 → x ∈ nonZeroDivisors B := fun x hx => by
    obtain ⟨n, u, rfl⟩ := key x hx
    exact mul_mem (pow_mem ht n) u.isUnit.mem_nonZeroDivisors
  have : NoZeroDivisors B := ⟨fun {a b} hab => by
    by_contra hc
    push Not at hc
    exact hc.1 (mem_nonZeroDivisors_iff_right.mp (hreg b hc.2) a hab)⟩
  have : IsDomain B := NoZeroDivisors.to_isDomain B
  have hp : Prime t := by
    rw [← Ideal.span_singleton_prime (nonZeroDivisors.ne_zero ht), ← hm]
    infer_instance
  exact ⟨this, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨t, hp.irreducible, fun {x} hx => by
      obtain ⟨n, u, h⟩ := key x hx
      exact ⟨n, u, h⟩⟩⟩
end GlobalTheory
