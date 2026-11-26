-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_envelope_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:41:27.483405+00:00
-- url     : https://prove2.me/submissions/e4e7aa14-f1e7-4db1-8467-f38508873762

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The common grid envelope is integrable on each deterministic horizon. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (T : NNReal) :
    Integrable (envelope L Psi alpha beta T) P := by
  letI : IsProbabilityMeasure P := L.isProbability
  have hU := Kyprianou.Ch04.exercise47RunningSupremumIntegrable P F L T
  simp_rw [← Kyprianou.Ch04.kw47_runningSup_raw_eq L] at hU
  have hV : Integrable (fun w =>
      |beta-alpha| * runningSup L T w + ‖Psi alpha‖ * (T:Real)) P :=
    (hU.const_mul _).add (integrable_const _)
  exact (integrable_const (2:Real)).add (hV.const_mul _)
