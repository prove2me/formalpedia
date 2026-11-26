-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonStripMeasurableAmbientV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:32:07.9488+00:00
-- url     : https://prove2.me/submissions/0966369a-7292-431f-b192-40b7300011b7

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_pointFamilyRegionLintegralMeasurableV1
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
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (s t : ℝ) :
    Measurable (fun w => (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) := by
  have hm := pointFamilyRegionLintegralMeasurableV1 ((volume : Measure ℝ).prod Pi)
    K Z (Ioc s t ×ˢ Ioi (0 : ℝ)) (measurableSet_Ioc.prod measurableSet_Ioi)
    (fun z => ENNReal.ofReal z.2) (ENNReal.measurable_ofReal.comp measurable_snd)
  exact ENNReal.measurable_toReal.comp (hm.mono
    (prmEvalSigma_le hd.measurable_count hd.measurable_point _) le_rfl)
