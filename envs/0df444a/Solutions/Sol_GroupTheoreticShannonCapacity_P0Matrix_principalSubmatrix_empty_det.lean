-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_empty_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:44.226239+00:00
-- url     : https://prove2.me/submissions/38e970f2-52bf-47a8-a9ec-e384da1990ad

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (principalSubmatrix n M ∅).det = 1 := by
  simp only [principalSubmatrix, Finset.card_empty]
  exact Matrix.det_isEmpty
end GroupTheoreticShannonCapacity.P0Matrix
