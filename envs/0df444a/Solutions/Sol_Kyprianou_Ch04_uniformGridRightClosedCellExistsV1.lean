-- Prove2me | solution 1 for Kyprianou.Ch04.uniformGridRightClosedCellExistsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:27:37.891053+00:00
-- url     : https://prove2.me/submissions/3d76edb7-f567-4861-9825-0383eb799f6b

import Mathlib
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_unifGrid_cell_readable
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Every positive time on a compact horizon belongs to a uniform right-closed cell. -/
theorem solution (T r : NNReal) (hr : 0 < r) (hrT : r ≤ T) (n : ℕ) :
    ∃ i : ℕ, i < n+1 ∧ T * (i : NNReal) / ((n+1 : ℕ) : NNReal) < r ∧
      r ≤ T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal) := by
  obtain ⟨i,hi,hl,hu⟩ :=
    LevyStochCalc.Brownian.Ito.exists_unifGrid_cell_readable
      (T := (T : ℝ)) (by exact_mod_cast hr.trans_le hrT)
      (m := n+1) (by omega) (s := (r : ℝ))
      (by exact_mod_cast hr) (by exact_mod_cast hrT)
  unfold LevyStochCalc.Brownian.Ito.unifGrid at hl hu
  refine ⟨i,hi,?_,?_⟩
  · exact_mod_cast (show (T : ℝ) * (i : ℝ) / ((n+1 : ℕ) : ℝ) < (r : ℝ) from by simpa [mul_comm] using hl)
  · exact_mod_cast (show (r : ℝ) ≤ (T : ℝ) * ((i+1 : ℕ) : ℝ) / ((n+1 : ℕ) : ℝ) from by simpa [mul_comm] using hu)
