-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.matrixX_real_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:37.231164+00:00
-- url     : https://prove2.me/submissions/36575def-368a-4e4e-97c1-9b809115ae5e

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r s : ℕ) :
    matrixX_real n k b r s = (matrixX n k b r s).map (↑· : ℚ → ℝ) := by
  ext i j
  simp only [matrixX_real, matrixX, Matrix.of_apply, Matrix.map_apply]
  simp only [X_entry_real, X_entry, aReal, a]
  split_ifs with h1 h2
  · -- i < j case
    push_cast; ring
  · -- i > j case
    push_cast; ring
  · -- i = j case
    simp only [Rat.cast_zero]
end GroupTheoreticShannonCapacity.Construction
