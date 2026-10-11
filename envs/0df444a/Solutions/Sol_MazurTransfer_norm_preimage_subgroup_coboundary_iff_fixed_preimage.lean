-- Prove2me | solution 1 for MazurTransfer.norm_preimage_subgroup_coboundary_iff_fixed_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T20:07:06.27375+00:00
-- url     : https://prove2.me/submissions/e0e35cc8-cd17-4023-9d0d-e4143c91974f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: triviality of a kernel-valued preimage cocycle is
equivalent to the existence of an invariant preimage.
Named downstream consumer: the zero criterion for actual Picard norm
classes in Mathlib algebraic group cohomology.
-/
import Mathlib

namespace MazurTransfer.PublicNormCocycleInvariantPreimageCriterion
variable {G H : Type} [Group G] [CommGroup H]
variable (ρ : G → H →* H) (f : H →* H)

theorem coboundary_iff_invariant_preimage {a b : H} (hb : f b = a) :
    (∃ z : f.ker, ∀ σ, ρ σ z.val * z.val⁻¹ = ρ σ b * b⁻¹) ↔
      ∃ c : H, f c = a ∧ ∀ σ, ρ σ c = c := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨b * z.val⁻¹, ?_, ?_⟩
    · have hz0 : f z.val = 1 := z.property
      simp only [map_mul, map_inv, hb, hz0, inv_one, mul_one]
    · intro σ
      have hσ : ρ σ b = (ρ σ z.val * z.val⁻¹) * b :=
        (mul_inv_eq_iff_eq_mul).mp (hz σ).symm
      rw [map_mul, map_inv, hσ]
      simp [mul_assoc, mul_left_comm, mul_comm]
  · rintro ⟨c, hc, hfixed⟩
    have hz : f (b * c⁻¹) = 1 := by simp only [map_mul, map_inv, hb, hc, mul_inv_cancel]
    refine ⟨⟨b * c⁻¹, hz⟩, ?_⟩
    intro σ
    simp only [map_mul, map_inv, hfixed]
    group

end MazurTransfer.PublicNormCocycleInvariantPreimageCriterion
theorem solution
    (G A : Type) [Group G] [CommGroup A] (ρ : G → A →* A) (φ : A →* A)
    (S : Subgroup G) (a b : A) (hb : φ b = a) :
    (∃ z : φ.ker, ∀ σ : S, ρ σ.val z.val * z.val⁻¹ = ρ σ.val b * b⁻¹) ↔
      ∃ c : A, φ c = a ∧ ∀ σ : S, ρ σ.val c = c := by
  exact MazurTransfer.PublicNormCocycleInvariantPreimageCriterion.coboundary_iff_invariant_preimage
    (fun σ : S => ρ σ.val) φ hb
#print axioms solution
