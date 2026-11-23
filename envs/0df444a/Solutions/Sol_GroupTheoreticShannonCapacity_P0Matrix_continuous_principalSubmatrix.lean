-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.continuous_principalSubmatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:36.184519+00:00
-- url     : https://prove2.me/submissions/cb43fb1e-66f8-402e-aa0f-0ed9876d5c81

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (S : Finset (Fin n)) :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => principalSubmatrix n M S) := by
  unfold principalSubmatrix
  apply continuous_matrix
  intro i j
  exact continuous_apply_apply _ _
end GroupTheoreticShannonCapacity.P0Matrix
