-- Prove2me | solution 1 for GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:44.661484+00:00
-- url     : https://prove2.me/submissions/0c195a47-e1c9-4727-84b3-cbc5ce3ced5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumCompEqFinsumCardFiberMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Type} (π : X → Y) (h : Y → ℂ)
    (hf : (∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) :
    ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  classical
  by_cases hfin : (Function.support (h ∘ π)).Finite
  · set S := hfin.toFinset with hS
    have hmemS : ∀ x, x ∈ S ↔ h (π x) ≠ 0 := by
      intro x
      simp [hS]
    have hL : ∑ᶠ x, h (π x) = ∑ x ∈ S, h (π x) := by
      apply finsum_eq_sum_of_support_subset
      intro x hx
      exact (hmemS x).2 hx
    have hR : ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y
        = ∑ y ∈ S.image π, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
      apply finsum_eq_sum_of_support_subset
      intro y hy
      rw [Function.mem_support] at hy
      have h1 : h y ≠ 0 := right_ne_zero_of_mul hy
      have h2 : Nat.card (π ⁻¹' {y}) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hy
      obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp h2).1
      have hxy : π x = y := hx
      rw [Finset.coe_image]
      refine ⟨x, ?_, hxy⟩
      rw [Finset.mem_coe, hmemS, hxy]
      exact h1
    rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (g := π) (t := S.image π)
      (fun x hx => Finset.mem_image_of_mem π hx)]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
    have hne : h (π x₀) ≠ 0 := (hmemS x₀).1 hx₀
    have hfib : π ⁻¹' {π x₀} = ↑(S.filter (fun x => π x = π x₀)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Set.mem_ofPred_eq]
      constructor
      · intro hx
        refine ⟨?_, hx⟩
        rw [hmemS, hx]
        exact hne
      · exact fun hx => hx.2
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul, hfib, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  · rw [finsum_of_infinite_support (f := fun x => h (π x)) hfin]
    symm
    rcases hf with hf | hf
    · apply finsum_of_infinite_support
      intro hR
      apply hfin
      refine (hR.preimage' (f := π) ?_).subset ?_
      · intro y hy
        exact hf y (right_ne_zero_of_mul hy)
      · intro x hx
        simp only [Function.mem_support, Function.comp_apply] at hx
        simp only [Set.mem_preimage, Function.mem_support]
        have hfinx : Finite (π ⁻¹' {π x}) := (hf (π x) hx).to_subtype
        have hnx : Nonempty (π ⁻¹' {π x}) := ⟨⟨x, rfl⟩⟩
        have hc : Nat.card (π ⁻¹' {π x}) ≠ 0 := Nat.card_ne_zero.mpr ⟨hnx, hfinx⟩
        exact mul_ne_zero (by exact_mod_cast hc) hx
    · have hz : (fun y => (Nat.card (π ⁻¹' {y}) : ℂ) * h y) = fun _ => 0 := by
        funext y
        by_cases hy : h y = 0
        · simp [hy]
        · simp [hf y hy]
      rw [hz, finsum_zero]
end GlobalTheory
