-- Prove2me | solution 1 for GlobalTheory.span_image_eq_span_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:36.100306+00:00
-- url     : https://prove2.me/submissions/c06bc65e-395d-4c33-82b4-115e66ebeee8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFiniteExtensionCapitulationComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E M : Type} [Field E] [Field M] (ψ : E →+* M)
    (I : Submodule (𝓞 E) E) (n : ℕ) (β : E) (hβ : I ^ (n + 1) = Submodule.span (𝓞 E) {β})
    (γ : M) (hγ : γ ^ (n + 1) = ψ β) :
    Submodule.span (𝓞 M) (ψ '' I) = Submodule.span (𝓞 M) {γ} := by
  set J := Submodule.span (𝓞 M) (ψ '' I) with hJ
  have hint : ∀ c : 𝓞 E, IsIntegral ℤ (ψ c) := fun c =>
    map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe c)
  have hle : J ≤ Submodule.span (𝓞 M) {γ} := by
    rw [hJ, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ^ (n + 1) ∈ Submodule.span (𝓞 E) {β} := hβ ▸ Submodule.pow_mem_pow I hx (n + 1)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxn
    have hc' : ψ x ^ (n + 1) = ψ c * γ ^ (n + 1) := by
      rw [hγ, ← map_pow, ← hc, ← map_mul]; rfl
    by_cases hγ0 : γ = 0
    · have : ψ x = 0 := by
        rw [hγ0] at hc'
        simpa using hc'
      rw [this]; exact Submodule.zero_mem _
    · have hi : IsIntegral ℤ (ψ x / γ) := by
        apply IsIntegral.of_pow (Nat.succ_pos n)
        rw [div_pow, hc', mul_div_assoc, div_self (pow_ne_zero _ hγ0), mul_one]
        exact hint c
      refine Submodule.mem_span_singleton.mpr ⟨⟨ψ x / γ, hi⟩, ?_⟩
      change (ψ x / γ) * γ = ψ x
      exact div_mul_cancel₀ _ hγ0
  have hpow : ∀ k : ℕ, ∀ y ∈ I ^ k, ψ y ∈ J ^ k := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy ⊢
      obtain ⟨c, rfl⟩ := hy
      exact ⟨⟨ψ c, hint c⟩, rfl⟩
    | succ k ih =>
      intro y hy
      rw [pow_succ] at hy ⊢
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (ih a ha) (Submodule.subset_span ⟨b, hb, rfl⟩)
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
  refine le_antisymm hle ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  by_cases hγ0 : γ = 0
  · rw [hγ0]; exact Submodule.zero_mem _
  have h1 : γ ^ (n + 1) ∈ J ^ (n + 1) := by
    rw [hγ]; apply hpow; rw [hβ]; exact Submodule.mem_span_singleton_self β
  have h2 : J ^ (n + 1) ≤ J * Submodule.span (𝓞 M) {γ ^ n} := by
    rw [pow_succ']
    refine mul_le_mul_right ?_ _
    rw [← Set.singleton_pow, ← Submodule.span_pow]
    exact pow_le_pow_left' hle n
  obtain ⟨z, hz, hz'⟩ := Submodule.mem_mul_span_singleton.mp (h2 h1)
  rw [pow_succ'] at hz'
  have : z = γ := mul_right_cancel₀ (pow_ne_zero n hγ0) hz'
  exact this ▸ hz
end GlobalTheory
