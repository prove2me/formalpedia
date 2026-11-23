-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.isP0_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:42.219026+00:00
-- url     : https://prove2.me/submissions/5d702608-1162-4737-848a-048a912470d1

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isClosed_principalMinor_nonneg

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) : IsClosed {M : Matrix (Fin n) (Fin n) ℝ | IsP0Matrix n M} := by
  have h : {M : Matrix (Fin n) (Fin n) ℝ | IsP0Matrix n M} =
      ⋂ S : Finset (Fin n), {M | (principalSubmatrix n M S).det ≥ 0} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_iInter, IsP0Matrix]
  rw [h]
  apply isClosed_iInter
  intro S
  exact isClosed_principalMinor_nonneg n S
end GroupTheoreticShannonCapacity.P0Matrix
