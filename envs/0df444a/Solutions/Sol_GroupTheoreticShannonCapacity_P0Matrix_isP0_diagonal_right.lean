-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.isP0_diagonal_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:23.453499+00:00
-- url     : https://prove2.me/submissions/adf6b251-0a16-45be-bdf6-0f0d0377c49a

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_mul_diagonal

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    IsP0Matrix n (M * diagonal d) := by
  intro S
  rw [principalSubmatrix_mul_diagonal]
  rw [Matrix.det_mul, Matrix.det_diagonal]
  apply mul_nonneg
  · exact hM S
  · apply Finset.prod_nonneg
    intro i _
    exact hd (S.orderEmbOfFin rfl i)
end GroupTheoreticShannonCapacity.P0Matrix
