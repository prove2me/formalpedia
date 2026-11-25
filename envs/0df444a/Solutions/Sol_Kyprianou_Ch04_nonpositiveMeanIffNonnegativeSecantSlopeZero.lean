-- Prove2me | solution 1 for Kyprianou.Ch04.nonpositiveMeanIffNonnegativeSecantSlopeZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:33:16.842989+00:00
-- url     : https://prove2.me/submissions/7495b441-c3ed-4760-ad2d-d17614b906a9

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity
open Set
set_option autoImplicit false

/-- Nonpositive secant slope is equivalent to the epsilon-slope criterion. -/
theorem solution (f : ℝ → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧ f θ < ε * θ) ↔
      max 0 (sInf ((fun θ : ℝ => f θ / θ) '' Set.Ioi 0)) = 0 := by
  let S : Set ℝ := (fun θ : ℝ => f θ / θ) '' Ioi 0
  have hne : S.Nonempty := ⟨f 1 / 1, 1, by norm_num, rfl⟩
  change (∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧ f θ < ε * θ) ↔
    max 0 (sInf S) = 0
  constructor
  · intro hmean
    apply max_eq_left
    by_cases hb : BddBelow S
    · by_contra hs
      have hpos : 0 < sInf S := lt_of_not_ge hs
      obtain ⟨θ, hθ, hθeps⟩ := hmean (sInf S / 2) (by positivity)
      have hmem : f θ / θ ∈ S := ⟨θ, hθ, rfl⟩
      have hlower : sInf S ≤ f θ / θ := csInf_le hb hmem
      have hupper : f θ / θ < sInf S / 2 :=
        (div_lt_iff₀ hθ).2 hθeps
      linarith
    · rw [Real.sInf_of_not_bddBelow hb]
  · intro hmax ε hε
    have hle : sInf S ≤ 0 := by
      have hh : sInf S ≤ max 0 (sInf S) := le_max_right _ _
      simpa [hmax] using hh
    by_contra hn
    push_neg at hn
    have hbound : ∀ x ∈ S, ε ≤ x := by
      rintro x ⟨θ, hθ, rfl⟩
      exact (le_div_iff₀ hθ).2 (hn θ hθ)
    have hlower : ε ≤ sInf S := le_csInf hne hbound
    linarith
