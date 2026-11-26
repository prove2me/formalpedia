-- Prove2me | solution 1 for Kyprianou.Ch05.pointFamilyPositiveFibreExistsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:26:56.755127+00:00
-- url     : https://prove2.me/submissions/41be13fe-74de-497f-a713-6124c1679207

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_pointFamilyPairLIntegralV1
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
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega) (t : ℝ)
    (hpos : 0 < (∫⁻ z in {t} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
      ∂(poissonRandomMeasure K Z w)).toReal) :
    ∃ i : ℕ × ℕ, i.2 < K i.1 w ∧ (Z i.1 i.2 w).1 = t ∧ 0 < (Z i.1 i.2 w).2 := by
  classical
  by_contra! h
  let S := {t} ×ˢ Ioi (0 : ℝ)
  have hS : MeasurableSet S := (measurableSet_singleton _).prod measurableSet_Ioi
  let g : ℝ × ℝ → ENNReal := S.indicator (fun z => ENNReal.ofReal z.2)
  have hg : Measurable g := (ENNReal.measurable_ofReal.comp measurable_snd).indicator hS
  have he : (∫⁻ z in S, ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) = 0 := by
    rw [← lintegral_indicator hS,pointFamilyPairLIntegralV1 K Z w g hg,ENNReal.tsum_eq_zero]
    intro i
    by_cases hi : i.2 < K i.1 w
    · rw [if_pos hi]
      apply Set.indicator_of_notMem
      intro hm
      exact (not_lt_of_ge (h i hi hm.1)) hm.2
    · exact if_neg hi
  change 0 < (∫⁻ z in S, ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal at hpos
  rw [he,ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos
