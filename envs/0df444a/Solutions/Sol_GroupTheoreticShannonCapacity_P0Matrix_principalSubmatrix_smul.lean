-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:18.7588+00:00
-- url     : https://prove2.me/submissions/45d8b03b-001b-4257-b8b4-893df61c336e

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (S : Finset (Fin n)) :
    principalSubmatrix n (c • M) S = c • principalSubmatrix n M S := by
  unfold principalSubmatrix
  ext i j
  simp [Matrix.submatrix, Matrix.smul_apply]
end GroupTheoreticShannonCapacity.P0Matrix
