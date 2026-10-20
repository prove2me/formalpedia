-- Prove2me | solution 1 for MazurTransfer.original_scalar_cocycle_character_kernel_detection_and_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T13:34:20.805318+00:00
-- url     : https://prove2.me/submissions/04db7b24-2b61-4838-af07-e5478613a4cc

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a scalar-character cocycle vanishing on the same character kernel is a coboundary, for an arbitrary group and field. All original cocycle and kernel-vanishing hypotheses are retained.
Named downstream consumer: injective restriction of the original continuous reflected-character H1 to its coefficient-trivializing subgroup, then its genuine kernel characters.
-/
import Mathlib
noncomputable section
namespace MazurTransfer.ScalarCocycleKernelDetectionProofBoundary20261019
end MazurTransfer.ScalarCocycleKernelDetectionProofBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a scalar character cocycle vanishing on the character
kernel is a coboundary. No finite group or finite image is assumed.
Named downstream consumer: injective restriction of the ACTUAL reflected
character H1 classes to their coefficient-trivializing subgroup.
-/

noncomputable section
namespace MazurTransfer.OriginalScalarCocycleKernelDetectionProof20261019
variable {k G : Type} [Field k] [Group G]
variable (χ : G →* kˣ) (c : G → k)
variable (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h)
variable (hzero : ∀ g, χ g = 1 → c g = 0)
include hc hzero

theorem apply_eq_of_character_eq (g h : G) (he : χ g = χ h) : c g = c h := by
  have hk : χ (g * h⁻¹) = 1 := by rw [map_mul, map_inv, he, mul_inv_cancel]
  have ht := hc (g * h⁻¹) h
  rw [hzero _ hk, hk, Units.val_one, zero_add, one_mul] at ht
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using ht

theorem scalar_cross_relation (g h : G) :
    ((χ g : k) - 1) * c h = ((χ h : k) - 1) * c g := by
  have he : χ (g * h) = χ (h * g) := by rw [map_mul, map_mul, mul_comm]
  have ht := apply_eq_of_character_eq χ c hc hzero (g * h) (h * g) he
  rw [hc g h, hc h g] at ht
  linear_combination ht

theorem exists_coboundary : ∃ a : k, ∀ g, c g = (χ g : k) * a - a := by
  by_cases htriv : ∀ g, χ g = 1
  · exact ⟨0, fun g => by rw [hzero g (htriv g), mul_zero, sub_zero]⟩
  · push Not at htriv
    obtain ⟨g, hg⟩ := htriv
    have hne : (χ g : k) - 1 ≠ 0 := sub_ne_zero.mpr (by
      intro he
      apply hg
      apply Units.ext
      exact he)
    refine ⟨c g / ((χ g : k) - 1), ?_⟩
    intro h
    have ht := scalar_cross_relation χ c hc hzero g h
    apply (mul_left_cancel₀ hne)
    field_simp
    linear_combination ht

end MazurTransfer.OriginalScalarCocycleKernelDetectionProof20261019

theorem solution : (∀ {k G : Type} [Field k] [Group G] (χ : G →* kˣ) (c : G → k) (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h) (hzero : ∀ g, χ g = 1 → c g = 0) (g h : G) (he : χ g = χ h), c g = c h) ∧ (∀ {k G : Type} [Field k] [Group G] (χ : G →* kˣ) (c : G → k) (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h) (hzero : ∀ g, χ g = 1 → c g = 0) (g h : G), ((χ g : k) - 1) * c h = ((χ h : k) - 1) * c g) ∧ (∀ {k G : Type} [Field k] [Group G] (χ : G →* kˣ) (c : G → k) (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h) (hzero : ∀ g, χ g = 1 → c g = 0), ∃ a : k, ∀ g, c g = (χ g : k) * a - a) := by
  exact ⟨MazurTransfer.OriginalScalarCocycleKernelDetectionProof20261019.apply_eq_of_character_eq, MazurTransfer.OriginalScalarCocycleKernelDetectionProof20261019.scalar_cross_relation, MazurTransfer.OriginalScalarCocycleKernelDetectionProof20261019.exists_coboundary⟩
#print axioms solution
