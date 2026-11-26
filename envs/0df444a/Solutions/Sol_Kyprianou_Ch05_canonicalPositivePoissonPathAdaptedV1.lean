-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonPathAdaptedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:19:41.483807+00:00
-- url     : https://prove2.me/submissions/d8cafcbc-8e2a-4fbe-a391-3a278e665e76

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
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (F : Filtration NNReal inferInstance)
    (hF : ∀ t : NNReal, F t = prmEvalSigma K Z ((volume : Measure ℝ).prod Pi)
      (Iic (t : ℝ) ×ˢ univ))
    (d : ℝ) :
    Adapted F (fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) := by
  intro t
  rw [hF t]
  have hsub : Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ) ⊆ Iic (t : ℝ) ×ˢ (univ : Set ℝ) :=
    fun z hz => ⟨hz.1.2,mem_univ _⟩
  have hm := pointFamilyRegionLintegralMeasurableV1 ((volume : Measure ℝ).prod Pi)
    K Z (Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ))
    (measurableSet_Ioc.prod measurableSet_Ioi) (fun z => ENNReal.ofReal z.2)
    (ENNReal.measurable_ofReal.comp measurable_snd)
  exact (ENNReal.measurable_toReal.comp
    (hm.mono (prmEvalSigma_mono hsub) le_rfl)).const_add _
