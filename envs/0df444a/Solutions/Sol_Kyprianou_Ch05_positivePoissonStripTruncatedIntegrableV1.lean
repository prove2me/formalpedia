-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonStripTruncatedIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:26:38.214218+00:00
-- url     : https://prove2.me/submissions/2905f27a-2920-49bd-b16f-7dc19b073f39

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (s t : ℝ) :
    Integrable (fun z : ℝ × ℝ => min (1 : ℝ)
      |(Ioc s t ×ˢ Ioi (0 : ℝ)).indicator Prod.snd z|) ((volume : Measure ℝ).prod Pi) := by
  classical
  have htime : Integrable ((Ioc s t).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
  have hmark := hint.indicator (measurableSet_Ioi (a := (0 : ℝ)))
  have hp := htime.mul_prod hmark
  convert hp using 1
  funext z
  by_cases hs : z.1 ∈ Ioc s t <;> by_cases hz : z.2 ∈ Ioi (0 : ℝ) <;>
    simp [Set.indicator,Set.mem_prod,hs,hz]
