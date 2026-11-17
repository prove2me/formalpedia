-- Prove2me | solution 1 for N25.Alg.exists_invariant_quadratic_of_pow_five
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:22:00.144545+00:00
-- url     : https://prove2.me/submissions/270007f6-158b-4afe-8d12-2847894617a7

import Mathlib

namespace N25.Alg

/-- Summing over the five iterates gives an invariant quadratic height with finite sublevels. -/
theorem _root_.solution {G : Type*} [AddCommGroup G] (g : G →+ G)
    (hg : ∀ x, g (g (g (g (g x)))) = x) (q₀ : G → ℝ) (hnn : ∀ x, 0 ≤ q₀ x)
    (hpar : ∀ x y, q₀ (x + y) + q₀ (x - y) = 2 * q₀ x + 2 * q₀ y)
    (hN : ∀ B : ℝ, {x | q₀ x ≤ B}.Finite) :
    ∃ q : G → ℝ, (∀ x, 0 ≤ q x) ∧ (∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y) ∧
      (∀ x, q (g x) = q x) ∧ ∀ B : ℝ, {x | q x ≤ B}.Finite := by
  refine ⟨fun x => q₀ x + q₀ (g x) + q₀ (g (g x)) + q₀ (g (g (g x))) +
      q₀ (g (g (g (g x)))), ?_, ?_, ?_, ?_⟩
  · intro x
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (hnn x) (hnn (g x)))
      (hnn (g (g x)))) (hnn (g (g (g x))))) (hnn (g (g (g (g x)))))
  · intro x y
    simp only [map_add, map_sub]
    have h₀ := hpar x y
    have h₁ := hpar (g x) (g y)
    have h₂ := hpar (g (g x)) (g (g y))
    have h₃ := hpar (g (g (g x))) (g (g (g y)))
    have h₄ := hpar (g (g (g (g x)))) (g (g (g (g y))))
    linarith
  · intro x
    dsimp only
    rw [hg]
    ring
  · intro B
    apply (hN B).subset
    intro x hx
    have h₁ := hnn (g x)
    have h₂ := hnn (g (g x))
    have h₃ := hnn (g (g (g x)))
    have h₄ := hnn (g (g (g (g x))))
    change q₀ x ≤ B
    change q₀ x + q₀ (g x) + q₀ (g (g x)) + q₀ (g (g (g x))) +
      q₀ (g (g (g (g x)))) ≤ B at hx
    linarith

end N25.Alg
