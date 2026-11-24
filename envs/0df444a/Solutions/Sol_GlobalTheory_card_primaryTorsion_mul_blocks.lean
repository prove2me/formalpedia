-- Prove2me | solution 1 for GlobalTheory.card_primaryTorsion_mul_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:54.523291+00:00
-- url     : https://prove2.me/submissions/1e40d497-6931-4dec-8f08-50364b063c15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers
import Theorems.Thm_GlobalTheory_PrimaryTorsionBlocks_card_killedBy_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.PrimaryTorsionBlocks
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0}) →
    (∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    ∃ e : ℕ, 1 ≤ e ∧ ∀ j : ℕ, Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * (j + 1)), a • x = 0} =
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * j), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ e, a • x = 0} := by
  classical
  intro F _ _ M _ _ N hN _ hlift 𝔭 h𝔭 hN𝔭
  have hne : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hI : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨Q, hPQ, hspan⟩ := Ideal.eq_prime_pow_mul_coprime hI 𝔭
  refine ⟨Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(N : 𝓞 F)})),
    ?_, fun j => ?_⟩
  · by_contra h0
    have h0' : Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(N : 𝓞 F)})) = 0 := by omega
    rw [h0', pow_zero, one_mul] at hspan
    have hQ : Q ≤ 𝔭 := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact hN𝔭
    rw [sup_eq_left.2 hQ] at hPQ
    exact h𝔭.ne_top hPQ
  · have hlift' : ∀ j : ℕ, ∀ y : M, (N : 𝓞 F) ^ j • y = 0 →
        ∃ z : M, (N : 𝓞 F) ^ (j + 1) • z = 0 ∧ (N : 𝓞 F) • z = y := by
      intro j y hy
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hy
      obtain ⟨z, h1, h2⟩ := hlift j y hy
      refine ⟨z, ?_, ?_⟩
      · rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact h1
      · rw [Nat.cast_smul_eq_nsmul]; exact h2
    exact card_killedBy_block 𝔭 Q (N : 𝓞 F) _ hspan hPQ hlift' j
end GlobalTheory
