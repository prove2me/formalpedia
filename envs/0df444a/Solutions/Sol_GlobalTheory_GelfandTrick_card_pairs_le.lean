-- Prove2me | solution 1 for GlobalTheory.GelfandTrick.card_pairs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:37:53.094827+00:00
-- url     : https://prove2.me/submissions/4be06d05-d8c9-4ac0-9365-757a50b667f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Theorems.Thm_GlobalTheory_GelfandTrick_InDoubleCoset_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open GlobalTheory.GelfandTrick
variable {G : Type} [Group G]
open Classical
namespace GlobalTheory.GelfandTrick
theorem _root_.solution (J : Subgroup G) (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hinv : ∀ a, τ (τ a) = a) (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂)
    (hJ : ∀ k ∈ J, τ k ∈ J) (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, InDoubleCoset J α γ)
    (hR' : ∀ x : G, InDoubleCoset J α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, InDoubleCoset J β γ)
    (hS' : ∀ x : G, InDoubleCoset J β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J) (c : G ⧸ J) :
    ((R ×ˢ S).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card ≤
      ((S ×ˢ R).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have hone : τ 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹ := fun a => by
    have := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hτdc : ∀ a y, InDoubleCoset J a y → InDoubleCoset J a (τ y) := fun a y h => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hdc y
    exact h.mul hk₁ hk₂ e
  obtain ⟨k₁, hk₁, k₂, hk₂, hx⟩ := hdc x
  refine Finset.card_le_card_of_forall_subsingleton
    (fun p q => q.1⁻¹ * (x * k₂ * (τ p.1)⁻¹) ∈ J) ?_ ?_
  · rintro ⟨γ, δ⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp
    obtain ⟨⟨hγ, hδ⟩, hj⟩ := hp
    have h1 : τ x = τ ((γ * δ)⁻¹ * x) * τ δ * τ γ := by
      rw [← hmul, ← hmul]; congr 1; group
    have h2 : InDoubleCoset J β (x * k₂ * (τ γ)⁻¹) := by
      refine (hτdc _ _ (hS δ hδ)).mul (J.mul_mem (J.inv_mem hk₁) (hJ _ hj)) J.one_mem ?_
      have : x * k₂ = k₁⁻¹ * τ x := by rw [hx]; group
      rw [this, h1]; group
    obtain ⟨δ', ⟨hδ', hj'⟩, -⟩ := hS' _ h2
    have h3 : InDoubleCoset J α (δ'⁻¹ * x) :=
      (hτdc _ _ (hR γ hγ)).mul hj' (J.inv_mem hk₂) (by group)
    obtain ⟨γ', ⟨hγ', hj''⟩, -⟩ := hR' _ h3
    refine ⟨(δ', γ'), ?_, hj'⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨hδ', hγ'⟩, ?_⟩
    rwa [mul_inv_rev, mul_assoc]
  · rintro ⟨δ', γ'⟩ - ⟨γ₁, δ₁⟩ h₁ ⟨γ₂, δ₂⟩ h₂
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_product,
      QuotientGroup.eq, Finset.mem_coe] at h₁ h₂
    obtain ⟨⟨⟨hγ₁, hδ₁⟩, hj₁⟩, hr₁⟩ := h₁
    obtain ⟨⟨⟨hγ₂, hδ₂⟩, hj₂⟩, hr₂⟩ := h₂
    have h4 : γ₂⁻¹ * γ₁ ∈ J := by
      have := hJ _ (J.mul_mem (J.inv_mem hr₁) hr₂)
      have e : (δ'⁻¹ * (x * k₂ * (τ γ₁)⁻¹))⁻¹ * (δ'⁻¹ * (x * k₂ * (τ γ₂)⁻¹))
          = τ (γ₂⁻¹ * γ₁) := by rw [hmul, hτinv]; group
      rwa [e, hinv] at this
    have hγ : γ₁ = γ₂ :=
      (hR' γ₁ (hR γ₁ hγ₁)).unique ⟨hγ₁, by simpa using J.one_mem⟩ ⟨hγ₂, h4⟩
    subst hγ
    have h5 : InDoubleCoset J β (γ₁⁻¹ * x) := (hS δ₁ hδ₁).mul J.one_mem hj₁ (by group)
    have hδ : δ₁ = δ₂ :=
      (hS' _ h5).unique ⟨hδ₁, by rwa [mul_inv_rev, mul_assoc] at hj₁⟩
        ⟨hδ₂, by rwa [mul_inv_rev, mul_assoc] at hj₂⟩
    rw [hδ]
end GlobalTheory.GelfandTrick
