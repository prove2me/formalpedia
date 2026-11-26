-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonCharFunV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:42:18.03746+00:00
-- url     : https://prove2.me/submissions/d51c7d59-e392-4163-b2b5-3f60b1686c61

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripCharacteristicV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripMeasurableAmbientV1
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
    (d : ℝ) (t : NNReal) (u : ℝ) :
    charFun (Q.map (fun w => d*(t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal)) u =
      Complex.exp (((t : ℝ) : ℂ) *
        (∫ y in Ioi (0 : ℝ), (Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1) ∂Pi)
        + ((d*(t : ℝ)*u : ℝ) : ℂ)*Complex.I) := by
  let G : Lambda → ℝ := fun w => (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
    ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  have hm : Measurable G := positivePoissonStripMeasurableAmbientV1 Q Pi K Z hd hint 0 t
  have he : Q.map (fun w => d*(t : ℝ)+G w) =
      (Q.map G).map (fun y => d*(t : ℝ)+y) := (Measure.map_map (by fun_prop) hm).symm
  change charFun (Q.map (fun w => d*(t : ℝ)+G w)) u = _
  rw [he,charFun_map_const_add]
  have hc := positivePoissonStripCharacteristicV1 Q Pi K Z hd hint 0 t u t.coe_nonneg
  change charFun (Q.map G) u = _ at hc
  rw [hc,← Complex.exp_add]
  congr 1
  simp [Real.inner_apply]
  <;> ring
