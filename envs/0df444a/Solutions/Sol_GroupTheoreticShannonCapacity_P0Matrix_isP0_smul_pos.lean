-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.isP0_smul_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:54.994106+00:00
-- url     : https://prove2.me/submissions/32c06447-1e4d-4feb-9db4-2e9c4f5c1a05

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_smul

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (c : ℝ) (hc : 0 < c) : IsP0Matrix n (c • M) := by
  intro S
  rw [principalSubmatrix_smul]
  rw [Matrix.det_smul]
  apply mul_nonneg
  · exact pow_nonneg (le_of_lt hc) _
  · exact hM S
end GroupTheoreticShannonCapacity.P0Matrix
