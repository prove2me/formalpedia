-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.continuous_principalSubmatrix_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:23.981494+00:00
-- url     : https://prove2.me/submissions/ba6cbdf4-c39a-48f2-bb6d-9217e8d022a9

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_continuous_principalSubmatrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (S : Finset (Fin n)) :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => (principalSubmatrix n M S).det) :=
  (continuous_principalSubmatrix n S).matrix_det
end GroupTheoreticShannonCapacity.P0Matrix
