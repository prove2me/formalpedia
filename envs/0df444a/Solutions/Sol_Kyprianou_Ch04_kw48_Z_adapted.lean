-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_Z_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:25.306079+00:00
-- url     : https://prove2.me/submissions/0fbdc375-031c-4a7b-aa55-86fa931e4019

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- All finite-time factors are measurable in the supplied filtration. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) :
    Measurable[F t] (Z L alpha beta t) ∧
    Measurable[F t] (E L Psi alpha t) ∧
    Measurable[F t] (H L Psi alpha beta t) := by
  have hU : Adapted F (runningSup L) := (runningSup_isDividendStrategy L).2.2.2
  have hUt := hU t
  have hXt := L.adapted t
  constructor
  · unfold Z
    fun_prop (disch := assumption)
  constructor
  · unfold E
    fun_prop (disch := assumption)
  · unfold H G
    fun_prop (disch := assumption)
