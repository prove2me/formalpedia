-- Prove2me | solution 1 for MazurTransfer.equivariant_norm_preimage_kernel_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T19:09:27.608437+00:00
-- url     : https://prove2.me/submissions/eeadca3f-3f11-4ee7-b9ea-29a08a56cbb4

import Mathlib
universe u v
namespace MazurTransfer.NormPreimageCocyclePublic
variable {G H : Type*} [Group G] [CommGroup H]
variable (ρ : G → H →* H) (f : H →* H)

def difference (b : H) (σ : G) : H := ρ σ b * b⁻¹

theorem difference_in_kernel (heq : ∀ σ x, f (ρ σ x) = ρ σ (f x))
    {a b : H} (hb : f b = a) (ha : ∀ σ, ρ σ a = a) (σ : G) :
    f (difference ρ b σ) = 1 := by
  simp only [difference, map_mul, map_inv, heq, hb, ha, mul_inv_cancel]

theorem difference_cocycle (hmul : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x))
    (b : H) (σ τ : G) :
    difference ρ b (σ * τ) = difference ρ b σ * ρ σ (difference ρ b τ) := by
  simp only [difference, hmul, map_mul, map_inv]
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem difference_one (hone : ∀ x, ρ 1 x = x) (b : H) :
    difference ρ b 1 = 1 := by
  simp only [difference, hone, mul_inv_cancel]

theorem change_preimage_in_kernel {a b b' : H} (hb : f b = a) (hb' : f b' = a) :
    f (b' * b⁻¹) = 1 := by
  simp only [map_mul, map_inv, hb, hb', mul_inv_cancel]

theorem change_preimage_coboundary (b b' : H) (σ : G) :
    difference ρ b' σ =
      ρ σ (b' * b⁻¹) * difference ρ b σ * (b' * b⁻¹)⁻¹ := by
  simp only [difference, map_mul, map_inv]
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem kernel_preserved (heq : ∀ σ x, f (ρ σ x) = ρ σ (f x))
    {z : H} (hz : f z = 1) (σ : G) : f (ρ σ z) = 1 := by
  rw [heq, hz, map_one]

end MazurTransfer.NormPreimageCocyclePublic

theorem solution
    (G : Type u) (H : Type v) [Group G] [CommGroup H]
    (ρ : G → H →* H) (f : H →* H)
    (hone : ∀ x, ρ 1 x = x)
    (hmul : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x))
    (heq : ∀ σ x, f (ρ σ x) = ρ σ (f x))
    (hsurj : Function.Surjective f) (a : H) (ha : ∀ σ, ρ σ a = a) :
    ∃ b : H, f b = a ∧
      (∀ σ, f (ρ σ b * b⁻¹) = 1) ∧
      (∀ σ τ, ρ (σ * τ) b * b⁻¹ = (ρ σ b * b⁻¹) * ρ σ (ρ τ b * b⁻¹)) ∧
      ρ 1 b * b⁻¹ = 1 ∧
      (∀ b' : H, f b' = a → f (b' * b⁻¹) = 1 ∧
        ∀ σ, ρ σ b' * b'⁻¹ = ρ σ (b' * b⁻¹) * (ρ σ b * b⁻¹) * (b' * b⁻¹)⁻¹) := by
  obtain ⟨b, hb⟩ := hsurj a
  refine ⟨b, hb, ?_, ?_, ?_, ?_⟩
  · exact MazurTransfer.NormPreimageCocyclePublic.difference_in_kernel ρ f heq hb ha
  · exact MazurTransfer.NormPreimageCocyclePublic.difference_cocycle ρ hmul b
  · exact MazurTransfer.NormPreimageCocyclePublic.difference_one ρ hone b
  · intro b' hb'
    exact ⟨MazurTransfer.NormPreimageCocyclePublic.change_preimage_in_kernel f hb hb',
      MazurTransfer.NormPreimageCocyclePublic.change_preimage_coboundary ρ b b'⟩

#print axioms solution
