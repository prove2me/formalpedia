-- Prove2me | solution 1 for Kyprianou.Ch04.stoppedPrimitiveMartingaleZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:21:37.254074+00:00
-- url     : https://prove2.me/submissions/cacdde04-ab32-4ad8-88c1-dcd47745e635

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedPrimitiveClockLipschitz
import Theorems.Thm_Kyprianou_Ch04_lipschitzMartingaleZero
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- A primitive of a bounded time density which is a martingale vanishes. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (g : ℝ → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᵐ w ∂P,
      (∀ t : NNReal, IntegrableOn (fun r => g r w) (Icc (0 : ℝ) (t : ℝ)) volume) ∧
      (∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)), ‖g r w‖ ≤ C))
    (hM : Martingale (fun (t : NNReal) w =>
      ∫ r in Icc (0 : ℝ) (t : ℝ), g r w ∂volume) F P) :
    ∀ t : NNReal, ∀ᵐ w ∂P, (∫ r in Icc (0 : ℝ) (t : ℝ), g r w ∂volume) = 0 := by
  let M := fun (t : NNReal) w => ∫ r in Icc (0 : ℝ) (t : ℝ), g r w ∂volume
  have h0 : ∀ᵐ w ∂P, M 0 w = 0 := by
    simp [M,MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hL (s t : NNReal) (hst : s ≤ t) :
      ∀ᵐ w ∂P, |M t w-M s w| ≤ C*((t:ℝ)-(s:ℝ)) := by
    filter_upwards [h] with w hw
    exact boundedPrimitiveClockLipschitz (fun r => g r w) C hC hw.1 hw.2 s t hst
  exact lipschitzMartingaleZero P F M hM h0 C hC hL
