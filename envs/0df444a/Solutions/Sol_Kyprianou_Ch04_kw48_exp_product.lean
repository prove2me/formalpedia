-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_exp_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:31.391627+00:00
-- url     : https://prove2.me/submissions/d3c3cf39-f9aa-4543-9f28-1e225b887186

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Factorise the reflected exponential as the product of the two factors. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    E L Psi alpha t w * H L Psi alpha beta t w = Z L alpha beta t w := by
  unfold E H G Z
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
