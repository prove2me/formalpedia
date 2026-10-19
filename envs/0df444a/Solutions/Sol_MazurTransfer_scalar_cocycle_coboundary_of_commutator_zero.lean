-- Prove2me | solution 1 for MazurTransfer.scalar_cocycle_coboundary_of_commutator_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T10:44:10.629485+00:00
-- url     : https://prove2.me/submissions/0c3e92b3-c497-408a-a282-f5897fbf1b4b

/- Copyright (c) 2026 Vas and contributors. Apache-2.0. Design boundary: standalone scalar cocycle criterion retaining original commutators. Named downstream consumer: original chi13 inertia restriction at thirteen. -/
import Mathlib

theorem solution
    {k G : Type} [Field k] [Group G]
    (χ : G →* kˣ) (c : G → k)
    (hc : ∀ g h, c (g * h) = c g + (χ g : k) * c h)
    (hcomm : ∀ g h, c (g⁻¹ * h⁻¹ * g * h) = 0)
    (hχ : ∃ g, χ g ≠ 1) :
    ∃ a : k, ∀ g, c g = (χ g : k) * a - a := by
  have cross : ∀ g h, ((χ g : k) - 1) * c h = ((χ h : k) - 1) * c g := by
    intro g h
    have he : (h * g) * (g⁻¹ * h⁻¹ * g * h) = g * h := by group
    have hz : c (g * h) = c (h * g) := by
      rw [← he, hc, hcomm, mul_zero, add_zero]
    rw [hc, hc] at hz
    linear_combination hz
  obtain ⟨g, hg⟩ := hχ
  have hne : (χ g : k) - 1 ≠ 0 := sub_ne_zero.mpr (by
    intro he
    exact hg (Units.ext he))
  refine ⟨c g / ((χ g : k) - 1), ?_⟩
  intro h
  have ht := cross g h
  apply mul_left_cancel₀ hne
  field_simp
  linear_combination ht

#print axioms solution
