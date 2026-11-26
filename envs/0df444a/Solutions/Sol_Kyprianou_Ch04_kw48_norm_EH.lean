-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_norm_EH
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:25.532055+00:00
-- url     : https://prove2.me/submissions/8a4d4aab-816e-4378-a915-e2c0c73e28a6

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Both exponential factors have deterministic modulus. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    ‖E L Psi alpha t w‖ = Real.exp ((t:Real)*(Psi alpha).re) ∧
    ‖H L Psi alpha beta t w‖ = Real.exp (-(t:Real)*(Psi alpha).re) := by
  constructor
  · unfold E
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re,Complex.mul_im]
  · unfold H G
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re,Complex.mul_im]
