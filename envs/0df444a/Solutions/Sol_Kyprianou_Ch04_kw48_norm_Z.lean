-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_norm_Z
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:24.252946+00:00
-- url     : https://prove2.me/submissions/c164595f-c9dc-4609-ae05-8af1268a4b69

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The two-parameter reflected characteristic exponential has unit norm. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    ‖Z L alpha beta t w‖ = 1 := by
  unfold Z
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]
