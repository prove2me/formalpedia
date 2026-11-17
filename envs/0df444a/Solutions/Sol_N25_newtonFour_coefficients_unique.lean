-- Prove2me | solution 1 for N25.newtonFour_coefficients_unique
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:02.94721+00:00
-- url     : https://prove2.me/submissions/0b78308b-d3a9-41a1-85fc-971172eaea14

import Definitions.Def_N25_GenusFourNumerator

/-! # Reconstruction from four counts and the genus-four functional equation

The hypotheses retain the degree bound, constant coefficient, Newton identities,
and functional equation explicitly. Geometric producers of these hypotheses are
separate from this integer-polynomial calculation.
-/

namespace N25

/-- The first four Newton identities uniquely determine four coefficients. -/
theorem _root_.solution
    {s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℤ}
    (ha : NewtonFourEquations s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄)
    (hb : NewtonFourEquations s₁ s₂ s₃ s₄ b₁ b₂ b₃ b₄) :
    a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ ∧ a₄ = b₄ := by
  rcases ha with ⟨ha₁, ha₂, ha₃, ha₄⟩
  rcases hb with ⟨hb₁, hb₂, hb₃, hb₄⟩
  have h₁ : a₁ = b₁ := by omega
  rw [h₁] at ha₂ ha₃ ha₄
  have h₂ : a₂ = b₂ := by omega
  rw [h₂] at ha₃ ha₄
  have h₃ : a₃ = b₃ := by omega
  rw [h₃] at ha₄
  exact ⟨h₁, h₂, h₃, by omega⟩

namespace Endgame

end Endgame

end N25
