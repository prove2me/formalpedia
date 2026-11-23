-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.isClosed_principalMinor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:35.3209+00:00
-- url     : https://prove2.me/submissions/d8b107b6-6ee6-42f5-ad8b-3780edafc41f

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_continuous_principalSubmatrix_det

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (S : Finset (Fin n)) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℝ | (principalSubmatrix n M S).det ≥ 0} := by
  have h : {M : Matrix (Fin n) (Fin n) ℝ | (principalSubmatrix n M S).det ≥ 0} =
      (fun M => (principalSubmatrix n M S).det) ⁻¹' (Set.Ici 0) := rfl
  rw [h]
  exact IsClosed.preimage (continuous_principalSubmatrix_det n S) isClosed_Ici
end GroupTheoreticShannonCapacity.P0Matrix
