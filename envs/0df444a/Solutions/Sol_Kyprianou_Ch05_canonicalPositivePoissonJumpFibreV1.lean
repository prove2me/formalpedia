-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonJumpFibreV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:20:44.36124+00:00
-- url     : https://prove2.me/submissions/b9a947fb-5db9-4ac9-9f3c-bfdac7cd197e

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positivePoissonPathIncrementStripV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonAllTimeMassFiniteV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCadlagMonotoneV1
import Theorems.Thm_Kyprianou_Ch05_positiveStripShrinkingLeftLimitV1
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
    ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      X t w - Function.leftLim (fun s => X s w) t =
        (∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
          ∂(poissonRandomMeasure K Z w)).toReal := by
  dsimp only
  filter_upwards [positivePoissonPathIncrementStripV1 Q Pi K Z hd hint d,
    positivePoissonAllTimeMassFiniteV1 Q Pi K Z hd hint,
    canonicalPositivePoissonCadlagMonotoneV1 Q Pi K Z hd hint d hdrift] with w hi hf hc
  intro t ht
  let X := fun s : NNReal => d*(s : ℝ)+(∫⁻ z in Ioc (0 : ℝ) (s : ℝ) ×ˢ Ioi (0 : ℝ),
    ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  let f := fun s : NNReal => (∫⁻ z in Ioc (s : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
    ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  letI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
  have hL : Tendsto (fun s => X t - X s) (nhdsWithin t (Iio t))
      (nhds (X t - Function.leftLim X t)) := tendsto_const_nhds.sub (hc.1.tendsto_leftLim t)
  have hD : Tendsto (fun s : NNReal => d*((t : ℝ)-(s : ℝ))) (nhdsWithin t (Iio t))
      (nhds 0) := by
    have h : Continuous (fun s : NNReal => d*((t : ℝ)-(s : ℝ))) := by fun_prop
    have htend := (h.continuousWithinAt (s := Iio t) (x := t)).tendsto
    simpa only [sub_self,mul_zero] using htend
  have hR := positiveStripShrinkingLeftLimitV1 (poissonRandomMeasure K Z w) t ht (hf t)
  have hEq : (fun s => X t - X s) =ᶠ[nhdsWithin t (Iio t)]
      (fun s => d*((t : ℝ)-(s : ℝ))+f s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hi s t hs.le
  have h := (hD.add hR).congr' hEq.symm
  simp only [zero_add] at h
  exact tendsto_nhds_unique hL h
