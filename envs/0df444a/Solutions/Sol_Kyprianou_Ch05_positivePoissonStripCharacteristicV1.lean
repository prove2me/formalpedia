-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonStripCharacteristicV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:32:12.279214+00:00
-- url     : https://prove2.me/submissions/020e51ec-e82e-415f-8b1b-703c9da9ac5b

import Mathlib
import Theorems.Thm_Kyprianou_poissonRandomMeasureIntegralLaws
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripTruncatedIntegrableV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripRealIntegralV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripExponentProductV1
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
    (s t u : ℝ) (hst : s ≤ t) :
    charFun (Q.map (fun w => (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal)) u =
      Complex.exp (((t-s : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ),
        (Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1) ∂Pi) := by
  classical
  let g : ℝ × ℝ → ℝ := (Ioc s t ×ˢ Ioi (0 : ℝ)).indicator Prod.snd
  have hg : Measurable g := measurable_snd.indicator (measurableSet_Ioc.prod measurableSet_Ioi)
  have hc := (Kyprianou.poissonRandomMeasureIntegralLaws Q
    ((volume : Measure ℝ).prod Pi) K Z hd g hg).2.1
      (positivePoissonStripTruncatedIntegrableV1 Pi hint s t) u
  have he : (fun w => ∫ z, g z ∂(poissonRandomMeasure K Z w)) =
      (fun w => (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) :=
    funext fun w => positivePoissonStripRealIntegralV1 (poissonRandomMeasure K Z w) s t
  rw [← he, hc]
  congr 1
  exact positivePoissonStripExponentProductV1 Pi s t u hst
