-- Prove2me | solution 1 for Kyprianou.ProofPreparation.unit_discontinuity_has_nonzero_left_jump
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:54.356108+00:00
-- url     : https://prove2.me/submissions/2e51de31-8726-49b7-82ce-295f415e7d8b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem unit_discontinuity_has_nonzero_left_jump
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l))
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hdisc : ¬ ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) t) :
    ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧ f t ≠ l := by
  obtain ⟨l, hl⟩ := hL t ht
  refine ⟨l, hl, fun hfl => hdisc ?_⟩
  subst hfl
  have hleft : ContinuousWithinAt f (Set.Iic t) t :=
    continuousWithinAt_Iio_iff_Iic.1 hl
  have hright := hR t ⟨ht.1.le, ht.2⟩
  have hU : Set.Icc (0:ℝ) 1 ⊆ Set.Iic t ∪ Set.Icc t 1 := by
    intro y hy
    rcases le_total y t with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hy.2⟩
  exact (hleft.union hright).mono hU

end Kyprianou.ProofPreparation

theorem solution
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l))
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hdisc : ¬ ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) t) :
    ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) ∧ f t ≠ l := by
  first
  | exact Kyprianou.ProofPreparation.unit_discontinuity_has_nonzero_left_jump
  | exact Kyprianou.ProofPreparation.unit_discontinuity_has_nonzero_left_jump ..
  | (apply Kyprianou.ProofPreparation.unit_discontinuity_has_nonzero_left_jump <;> assumption)
