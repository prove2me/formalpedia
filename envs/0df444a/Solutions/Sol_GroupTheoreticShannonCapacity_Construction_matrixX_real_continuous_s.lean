-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.matrixX_real_continuous_s
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:52.127131+00:00
-- url     : https://prove2.me/submissions/f7a66ed7-2897-4ec4-8f25-812504dd6c39

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r : ℝ) :
    Continuous (fun s => matrixX_real n k b r s) := by
  apply continuous_matrix
  intro i j
  simp only [matrixX_real, Matrix.of_apply, X_entry_real, aReal]
  split_ifs with h1 h2
  · -- i < j case: r * a'^(j-i-1) * s^(n-(j-i+1))
    refine Continuous.mul ?_ ?_
    · refine Continuous.mul continuous_const ?_
      refine Continuous.pow ?_ _
      have : Continuous (fun s => k * b ^ n + s * b + r) := by continuity
      exact this
    · exact continuous_id.pow _
  · -- i > j case: -k * a'^(n-(i-j+1)) * s^(i-j-1)
    refine Continuous.mul ?_ ?_
    · refine Continuous.mul continuous_const ?_
      refine Continuous.pow ?_ _
      have : Continuous (fun s => k * b ^ n + s * b + r) := by continuity
      exact this
    · exact continuous_id.pow _
  · -- i = j case
    exact continuous_const
end GroupTheoreticShannonCapacity.Construction
