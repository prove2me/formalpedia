-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonFixedTimeSliceZeroV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:55:47.301183+00:00
-- url     : https://prove2.me/submissions/dc14526f-704a-4f14-9fe1-4a76162c70bf

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
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (t : ℝ) :
    ∀ᵐ w ∂Q, poissonRandomMeasure K Z w ({t} ×ˢ (univ : Set ℝ)) = 0 := by
  let R : Set (ℝ × ℝ) := {t} ×ˢ univ
  have hR : MeasurableSet R := (measurableSet_singleton t).prod MeasurableSet.univ
  have hm := measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hR
  have he := lintegral_poissonRandomMeasure_apply hd hR
  have hz : ((volume : Measure ℝ).prod Pi) R = 0 := by
    simp [R,Measure.prod_prod]
  rw [hz] at he
  exact (lintegral_eq_zero_iff hm).mp he
