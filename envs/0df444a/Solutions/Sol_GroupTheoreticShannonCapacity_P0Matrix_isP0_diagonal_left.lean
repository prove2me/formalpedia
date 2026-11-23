-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.isP0_diagonal_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:09.744825+00:00
-- url     : https://prove2.me/submissions/baf4f02f-43c2-40a6-9067-0b5a96aab772

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_diagonal_mul

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    IsP0Matrix n (diagonal d * M) := by
  intro S
  rw [principalSubmatrix_diagonal_mul]
  rw [Matrix.det_mul, Matrix.det_diagonal]
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i _
    exact hd (S.orderEmbOfFin rfl i)
  · exact hM S
end GroupTheoreticShannonCapacity.P0Matrix
