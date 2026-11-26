-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonStripRealIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:32:07.307472+00:00
-- url     : https://prove2.me/submissions/a5f8c746-efa2-4d16-aae8-494d21e236af

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
    (mu : Measure (ℝ × ℝ)) (s t : ℝ) :
    (∫ z, (Ioc s t ×ˢ Ioi (0 : ℝ)).indicator Prod.snd z ∂mu) =
      (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2 ∂mu).toReal := by
  classical
  let R := Ioc s t ×ˢ Ioi (0 : ℝ)
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioi
  let g : ℝ × ℝ → ℝ := R.indicator Prod.snd
  have hg : Measurable g := measurable_snd.indicator hR
  have hn (z : ℝ × ℝ) : 0 ≤ g z := by
    by_cases hz : z ∈ R
    · exact (show 0 < z.2 from hz.2).le.trans_eq (by simp [g,hz])
    · simp [g,hz]
  change (∫ z, g z ∂mu) = _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hn) hg.aestronglyMeasurable]
  congr 1
  rw [← lintegral_indicator hR]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ R <;> simp [g,Set.indicator,hz]
