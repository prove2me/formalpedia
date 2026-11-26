-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonStripMassFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:19:42.304223+00:00
-- url     : https://prove2.me/submissions/a02de48f-8436-4b07-a25d-ae043c5534ae

import Mathlib
import Theorems.Thm_Kyprianou_poissonRandomMeasureIntegralLaws
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripTruncatedIntegrableV1
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
    ∀ᵐ w ∂Q, (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) < ⊤ := by
  classical
  let R := Ioc s t ×ˢ Ioi (0 : ℝ)
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioi
  let g : ℝ × ℝ → ℝ := R.indicator Prod.snd
  have hg : Measurable g := measurable_snd.indicator hR
  have hn (z : ℝ × ℝ) : 0 ≤ g z := by
    by_cases hz : z ∈ R
    · exact (show 0 < z.2 from hz.2).le.trans_eq (by simp [g,hz])
    · simp [g,hz]
  have hi := (Kyprianou.poissonRandomMeasureIntegralLaws Q
    ((volume : Measure ℝ).prod Pi) K Z hd g hg).1.mpr
      (positivePoissonStripTruncatedIntegrableV1 Pi hint s t)
  filter_upwards [hi] with w hw
  have hf := (hasFiniteIntegral_iff_ofReal (ae_of_all _ hn)).mp hw.hasFiniteIntegral
  have he : (fun z => ENNReal.ofReal (g z)) = R.indicator (fun z => ENNReal.ofReal z.2) := by
    funext z
    by_cases hz : z ∈ R <;> simp [g,Set.indicator,hz]
  rw [he,lintegral_indicator hR] at hf
  exact hf
