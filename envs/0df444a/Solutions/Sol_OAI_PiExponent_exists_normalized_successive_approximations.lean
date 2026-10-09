-- Prove2me | solution 1 for OAI.PiExponent.exists_normalized_successive_approximations
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T11:48:43.577987+00:00
-- url     : https://prove2.me/submissions/911799fc-7bd3-40c2-a674-9f899f8224be

import Lean
import Theorems.Thm_OAI_PiExponent_exists_successive_approximations
import Theorems.Thm_OAI_PiExponent_exists_normalized_selection_of_selector

theorem solution
    (nu X D : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ x : ℕ → ℝ,
      x 0 = 1 ∧
      (∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < x (n + 1)) ∧
      (∀ i, 1 ≤ x i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, x j) < x i) := by
  exact OAI.PiExponent.exists_normalized_selection_of_selector nu X D
    (OAI.PiExponent.exists_successive_approximations nu hnu hbad)

#print axioms solution
