-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonCadlagMonotoneV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:34:53.39665+00:00
-- url     : https://prove2.me/submissions/5709f1db-a0d9-4bea-8fb9-ed897202ddb4

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positivePoissonAllTimeMassFiniteV1
import Theorems.Thm_Kyprianou_Ch05_positiveStripCumulativeCadlagV1
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
    (d : ℝ) (hdrift : 0 ≤ d) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    ∀ᵐ w ∂Q, Monotone (fun t => X t w) ∧ IsCadlag (fun t => X t w) := by
  dsimp only
  filter_upwards [positivePoissonAllTimeMassFiniteV1 Q Pi K Z hd hint] with w hw
  obtain ⟨hm,hc⟩ := positiveStripCumulativeCadlagV1 (poissonRandomMeasure K Z w) hw
  have hdmono : Monotone (fun t : NNReal => d*(t : ℝ)) :=
    fun a b hab => mul_le_mul_of_nonneg_left (by exact_mod_cast hab) hdrift
  have hm' := hdmono.add hm
  refine ⟨hm',?_⟩
  intro t
  have hcont : Continuous (fun t : NNReal => d*(t : ℝ)) := by fun_prop
  refine ⟨hcont.continuousWithinAt.add (hc t).1,?_⟩
  exact ⟨_,hm'.tendsto_leftLim t⟩
