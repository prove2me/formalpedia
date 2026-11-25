-- Prove2me | solution 1 for Kyprianou.Ch04.runningInfimumAntitoneFromFiniteBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:58:47.222949+00:00
-- url     : https://prove2.me/submissions/66a196ff-9cfe-4799-84a3-808ad2b42051

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- The initial-interval infimum decreases as the horizon grows. -/
theorem solution
    (f : NNReal → ℝ)
    (hBound : ∀ t : NNReal, BddBelow (f '' Set.Iic t)) :
    Antitone (fun t : NNReal => sInf (f '' Set.Iic t)) := by
  intro t u htu
  have hne : (f '' Set.Iic t).Nonempty := by
    exact ⟨f 0, 0, by simp, rfl⟩
  have hsub : f '' Set.Iic t ⊆ f '' Set.Iic u := by
    rintro y ⟨s, hs, rfl⟩
    exact ⟨s, le_trans hs htu, rfl⟩
  apply le_csInf hne
  intro y hy
  exact csInf_le (hBound u) (hsub hy)
