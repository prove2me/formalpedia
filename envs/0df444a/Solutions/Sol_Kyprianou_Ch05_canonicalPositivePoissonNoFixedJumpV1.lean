-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonNoFixedJumpV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:58:59.885308+00:00
-- url     : https://prove2.me/submissions/3e2373e3-67fe-47d7-8b54-65b0b221b8ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonJumpFibreV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonFixedTimeSliceZeroV1
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
    (d : ℝ) (hdrift : 0 ≤ d)
    (t : NNReal) (ht : 0 < t) :
    let X := fun (s : NNReal) (w : Lambda) =>
      d * (s : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (s : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    ∀ᵐ w ∂Q, Function.leftLim (fun s => X s w) t = X t w := by
  dsimp only
  filter_upwards [canonicalPositivePoissonJumpFibreV1 Q Pi K Z hd hint d hdrift,
    positivePoissonFixedTimeSliceZeroV1 Q Pi K Z hd (t : ℝ)] with w hj hz
  have h := hj t ht
  have hzero : poissonRandomMeasure K Z w ({(t : ℝ)} ×ˢ Ioi (0 : ℝ)) = 0 :=
    measure_mono_null (Set.prod_mono le_rfl (subset_univ _)) hz
  rw [Measure.restrict_eq_zero.mpr hzero,lintegral_zero_measure,ENNReal.toReal_zero] at h
  exact (sub_eq_zero.mp h).symm
