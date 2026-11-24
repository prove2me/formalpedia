-- Prove2me | solution 1 for GlobalTheory.exists_mul_invol_eq_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:57.257066+00:00
-- url     : https://prove2.me/submissions/132b808a-f351-453e-86ac-a9c7824bbaac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed

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
theorem _root_.solution (k : Type) [Field k] [Finite k] (τ : k →+* k)
    (hτ : Function.Involutive τ) (hne : ∃ b : k, τ b ≠ b) (c : k) (hc : τ c = c) :
    ∃ a : k, a * τ a = c := by
  classical
  obtain ⟨b, hb⟩ := hne
  let F : Subfield k := τ.eqLocusField (RingHom.id k)
  have hd : b - τ b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)

  let f : F × F → k := fun p => (p.1 : k) + (p.2 : k) * b
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨α, β⟩ ⟨α', β'⟩ h
      have ea : τ (α : k) = α := α.2
      have eb : τ (β : k) = β := β.2
      have ea' : τ (α' : k) = α' := α'.2
      have eb' : τ (β' : k) = β' := β'.2
      have h0 : (α : k) + β * b = α' + β' * b := h
      have h1 : τ ((α : k) + β * b) = τ ((α' : k) + β' * b) := by rw [h0]
      rw [map_add, map_mul, map_add, map_mul, ea, eb, ea', eb'] at h1
      have hβ : (β : k) = β' := by
        have h2 : ((β : k) - β') * (b - τ b) = 0 := by linear_combination h0 - h1
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact sub_eq_zero.mp h3
        · exact absurd h3 hd
      have hα : (α : k) = α' := by
        rw [hβ] at h0
        linear_combination h0
      exact Prod.ext (Subtype.ext hα) (Subtype.ext hβ)
    · intro x
      have hβ : τ ((x - τ x) / (b - τ b)) = (x - τ x) / (b - τ b) := by
        rw [map_div₀, map_sub, map_sub, hτ x, hτ b, ← neg_sub x (τ x), ← neg_sub b (τ b),
          neg_div_neg_eq]
      have hm : (x - τ x) / (b - τ b) * (b - τ b) = x - τ x := div_mul_cancel₀ _ hd
      have hα : τ (x - (x - τ x) / (b - τ b) * b) = x - (x - τ x) / (b - τ b) * b := by
        rw [map_sub, map_mul, hβ]
        linear_combination hm
      refine ⟨(⟨x - (x - τ x) / (b - τ b) * b, hα⟩, ⟨(x - τ x) / (b - τ b), hβ⟩), ?_⟩
      show x - (x - τ x) / (b - τ b) * b + (x - τ x) / (b - τ b) * b = x
      ring
  have hcard : Nat.card k = Nat.card F ^ 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, sq]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hrank : Module.finrank F k = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := k)
    rw [hcard] at h
    exact (Nat.pow_right_injective hq h).symm

  let τ' : k ≃ₐ[F] k := AlgEquiv.ofBijective { τ with commutes' := fun r => r.2 } hτ.bijective
  have hτ' : ∀ x, τ' x = τ x := fun _ => rfl
  have hne1 : (1 : k ≃ₐ[F] k) ≠ τ' := by
    intro h
    apply hb
    rw [← hτ' b, ← h]
    rfl
  have hcardG : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hrank]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, τ'} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcardG, Finset.card_pair hne1]

  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F k ⟨c, hc⟩
  have h := Algebra.norm_eq_prod_automorphisms F a
  rw [ha, huniv, Finset.prod_pair hne1] at h
  refine ⟨a, ?_⟩
  calc a * τ a = (1 : k ≃ₐ[F] k) a * τ' a := rfl
    _ = c := h.symm
end GlobalTheory
