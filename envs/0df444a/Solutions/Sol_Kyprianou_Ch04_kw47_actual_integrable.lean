-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_actual_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:54:10.338744+00:00
-- url     : https://prove2.me/submissions/339dcb8d-036c-47c9-99f6-96bc872d14a2

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_adapted
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
import Theorems.Thm_Kyprianou_Ch04_kw47_pointwise_envelope
import Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Pointwise integrability of the Kella--Whitt process follows from
strong adaptedness and the integrable running-maximum envelope. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (t : NNReal) :
    let Z : NNReal → Ω → Real := fun r w =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    let J : NNReal → Ω → Real := fun r w =>
      ∫ x in Set.Icc (0:Real) (r:Real), Z x.toNNReal w ∂volume
    Integrable (fun w => L.ψ alpha * J t w + 1 -
      Z t w - alpha * runningSup L t w) P := by
  dsimp only
  letI : IsProbabilityMeasure P := L.isProbability
  have hAdapt := Kyprianou.Ch04.kw47_actual_adapted L alpha hAlpha
  have hU := Kyprianou.Ch04.exercise47RunningSupremumIntegrable P F L t
  simp_rw [← Kyprianou.Ch04.kw47_runningSup_raw_eq L] at hU
  have hC : Integrable (fun _ : Ω => |L.ψ alpha| * (t:Real) + 2) P :=
    integrable_const _
  apply (hC.add (hU.const_mul alpha)).mono'
    ((hAdapt t).mono (F.le t)).aestronglyMeasurable
  filter_upwards [] with w
  have h := Kyprianou.Ch04.kw47_pointwise_envelope P F L alpha hAlpha t t w le_rfl
  simp_rw [← Kyprianou.Ch04.kw47_runningSup_raw_eq L] at h
  simpa only [Real.norm_eq_abs,Pi.add_apply] using h
