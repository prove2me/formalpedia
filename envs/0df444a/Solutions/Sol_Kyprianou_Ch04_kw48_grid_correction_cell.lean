-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_grid_correction_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:45:37.540803+00:00
-- url     : https://prove2.me/submissions/4271bd7c-6b05-47af-9c58-f345b162e0f2

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_product
import Theorems.Thm_Kyprianou_Ch04_kw48_exponential_cell_product
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact complex product correction expressed in terms of the log-weight. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (a b : NNReal) (w : Ω) :
    E L Psi alpha b w*(H L Psi alpha beta b w-H L Psi alpha beta a w) =
      Z L alpha beta b w*
        (1-Complex.exp (-(G L Psi alpha beta b w-G L Psi alpha beta a w))) := by
  rw [← Kyprianou.Ch04.kw48_exp_product L Psi alpha beta b w]
  unfold E H
  rw [← Complex.exp_add]
  exact Kyprianou.Ch04.kw48_exponential_cell_product _ _ _
