-- Prove2me | solution 1 for GlobalTheory.card_leftCosets_doubleCoset_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:51.969804+00:00
-- url     : https://prove2.me/submissions/3006de5b-47bb-488b-9957-01f5f7b5df76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardLeftCosetsDoubleCosetInvEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (J : Subgroup G) (α : G) (R R' : Finset G), MeasurableSet (J : Set G) → ν J ≠ 0 → ν J ≠ ⊤ → (∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂) → (∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J) → (∀ γ ∈ R', ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α⁻¹ * k₂) → (∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α⁻¹ * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ J) → R.card = R'.card := by
  intro G _ _ _ ν _ _ J α R R' hJ h0 htop hR hRu hR' hR'u
  set S : Set G := {x | ∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂} with hS
  have hA : ∀ γ ∈ R, ∀ x, γ⁻¹ * x ∈ J → x ∈ S := by
    intro γ hγ x hx
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR γ hγ
    exact ⟨k₁, h₁, k₂ * ((k₁ * α * k₂)⁻¹ * x), J.mul_mem h₂ hx, by group⟩
  have hB : ∀ γ ∈ R', ∀ x, x * γ ∈ J → x ∈ S := by
    intro γ hγ x hx
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR' γ hγ
    exact ⟨x * (k₁ * α⁻¹ * k₂) * k₂⁻¹, J.mul_mem hx (J.inv_mem h₂), k₁⁻¹, J.inv_mem h₁, by group⟩
  have hBu : ∀ x ∈ S, ∃! γ, γ ∈ R' ∧ x * γ ∈ J := by
    rintro x ⟨k₁, h₁, k₂, h₂, hx⟩
    have := hR'u x⁻¹ ⟨k₂⁻¹, J.inv_mem h₂, k₁⁻¹, J.inv_mem h₁, by rw [hx]; group⟩
    simpa only [← mul_inv_rev, J.inv_mem_iff] using this
  have e1 : S = ⋃ γ ∈ R, (fun x => γ⁻¹ * x) ⁻¹' (J : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    exact ⟨fun hx => (hRu x hx).exists, fun ⟨γ, h, h'⟩ => hA γ h x h'⟩
  have e2 : S = ⋃ γ ∈ R', (fun x => x * γ) ⁻¹' (J : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    exact ⟨fun hx => (hBu x hx).exists, fun ⟨γ, h, h'⟩ => hB γ h x h'⟩
  have m1 : ν S = R.card * ν J := by
    rw [e1, measure_biUnion_finset]
    · simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      exact hab ((hRu x (hA a ha x hxa)).unique ⟨ha, hxa⟩ ⟨hb, hxb⟩)
    · intro b _
      exact measurable_const_mul _ hJ
  have m2 : ν S = R'.card * ν J := by
    rw [e2, measure_biUnion_finset]
    · simp only [measure_preimage_mul_right, Finset.sum_const, nsmul_eq_mul]
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      exact hab ((hBu x (hB a ha x hxa)).unique ⟨ha, hxa⟩ ⟨hb, hxb⟩)
    · intro b _
      exact measurable_mul_const _ hJ
  have := (ENNReal.mul_left_inj h0 htop).1 (m1.symm.trans m2)
  exact_mod_cast this
end GlobalTheory
