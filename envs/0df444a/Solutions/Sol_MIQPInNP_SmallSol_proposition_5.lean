-- Prove2me | solution 1 for MIQPInNP.SmallSol.proposition_5
-- status  : ACCEPTED   (disprove)
-- author  : @queelius
-- created : 2026-10-28T05:20:42.093031+00:00
-- url     : https://prove2.me/submissions/cf24fa31-5cdd-4dd2-9920-f3b3c23b5916

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

open MIQPInNP.SmallSol

namespace Queelius.MIQPEncoding

theorem empty_input_size (n : ℕ) :
    matSize (0 : Matrix (Fin 0) (Fin n) ℚ) + vecSize (0 : Fin 0 → ℚ) = 0 := by
  simp [matSize, vecSize]

theorem dimension_le_vecSize {n : ℕ} (x : Fin n → ℚ) : n ≤ vecSize x := by
  exact Nat.le_add_right _ _

theorem empty_system_feasible (n : ℕ) :
    ∃ x ∈ polyhedron (0 : Matrix (Fin 0) (Fin n) ℚ) (0 : Fin 0 → ℚ),
      IsMixedInt 0 x := by
  refine ⟨0, ?_, ?_⟩
  · simp [polyhedron]
  · simp [IsMixedInt]

theorem zero_vector_size (n : ℕ) : vecSize (0 : Fin n → ℚ) = 3 * n := by
  simp [vecSize, bitSize, Nat.size]
  omega

/-- Requiring every coordinate to be integral still leaves the empty system feasible. -/
theorem empty_system_integral (n : ℕ) :
    ∃ x ∈ polyhedron (0 : Matrix (Fin 0) (Fin n) ℚ) (0 : Fin 0 → ℚ),
      IsMixedInt n x := by
  refine ⟨0, ?_, ?_⟩
  · simp [polyhedron]
  · intro i hi
    exact ⟨0, by simp⟩

/-- A nonempty constraint row makes the existing matrix size charge for dimension. -/
theorem one_row_size_controls_dimension (n : ℕ) (A : Matrix (Fin 1) (Fin n) ℚ) :
    n ≤ matSize A := by
  simp only [matSize, one_mul]
  exact Nat.le_add_right _ _

end Queelius.MIQPEncoding

/-- The formal bound omits the ambient dimension when the system has no rows.
This negates the platform statement, not the source paper's MIP-in-NP result. -/
theorem solution :
    ¬ (∃ g : Polynomial ℕ, ∀ (n p m : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      (∃ x ∈ polyhedron A b, IsMixedInt p x) →
      ∃ xh : Fin n → ℚ, toReal xh ∈ polyhedron A b ∧ IsMixedInt p (toReal xh) ∧
        vecSize xh ≤ g.eval (matSize A + vecSize b)) := by
  rintro ⟨g, hg⟩
  obtain ⟨xh, _, _, hsize⟩ := hg (g.eval 0 + 1) 0 0 0 0
    (Queelius.MIQPEncoding.empty_system_feasible (g.eval 0 + 1))
  rw [Queelius.MIQPEncoding.empty_input_size] at hsize
  have hdim := Queelius.MIQPEncoding.dimension_le_vecSize xh
  omega
