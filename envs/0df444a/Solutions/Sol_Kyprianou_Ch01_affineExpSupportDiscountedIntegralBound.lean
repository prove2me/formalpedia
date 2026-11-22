-- Prove2me | solution 1 for Kyprianou.Ch01.affineExpSupportDiscountedIntegralBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:43:39.63183+00:00
-- url     : https://prove2.me/submissions/11b88aae-2c73-46b9-8831-4646ad7b7e6c

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- A positive-intercept exponential support transports its unit exponential moment. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (V : ℝ → ℝ)
    (K q phi y v A B : ℝ) (t : ℝ≥0)
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hZm : Measurable Z) (hVm : Measurable V)
    (hVbound : ∀ z, ‖V z‖ ≤ K)
    (hMaj : ∀ z, V z ≤ A + B * Real.exp (-phi * (z - v)))
    (hTouch : V y = A + B * Real.exp (-phi * (y - v)))
    (hMoment :
      Integrable (fun ω => Real.exp (-phi * Z ω - q * (t : ℝ))) P ∧
      (∫ ω, Real.exp (-phi * Z ω - q * (t : ℝ)) ∂P) = 1) :
    Real.exp (-q * (t : ℝ)) * (∫ ω, V (y + Z ω) ∂P) ≤ V y := by
  let M : Ω → ℝ := fun ω =>
    Real.exp (-phi * Z ω - q * (t : ℝ))
  let C : ℝ := B * Real.exp (-phi * (y - v)) * Real.exp (q * (t : ℝ))
  have hRep (ω : Ω) :
      A + B * Real.exp (-phi * ((y + Z ω) - v)) =
        A + C * M ω := by
    dsimp only [C, M]
    congr 1
    calc
      B * Real.exp (-phi * ((y + Z ω) - v)) =
        B * Real.exp (-phi * (y - v) +
          (q * (t : ℝ) + (-phi * Z ω - q * (t : ℝ)))) := by
            congr 1
            ring
      _ = B * Real.exp (-phi * (y - v)) *
          Real.exp (q * (t : ℝ)) *
          Real.exp (-phi * Z ω - q * (t : ℝ)) := by
            rw [Real.exp_add, Real.exp_add]
            ring
  have hValueMeas : Measurable (fun ω => V (y + Z ω)) :=
    hVm.comp (measurable_const.add hZm)
  have hValueInt : Integrable (fun ω => V (y + Z ω)) P :=
    Integrable.of_bound hValueMeas.aestronglyMeasurable K
      (Filter.Eventually.of_forall (fun ω => hVbound (y + Z ω)))
  have hSupportInt : Integrable
      (fun ω => A + B * Real.exp (-phi * ((y + Z ω) - v))) P := by
    have hi : Integrable (fun ω => A + C * M ω) P :=
      (integrable_const A).add (hMoment.1.const_mul C)
    convert hi using 1
    funext ω
    exact hRep ω
  have hSupportIntegral :
      (∫ ω, A + B * Real.exp (-phi * ((y + Z ω) - v)) ∂P) =
        A + C := by
    have heq : (fun ω => A + B * Real.exp (-phi * ((y + Z ω) - v))) =
        (fun ω => A + C * M ω) := funext hRep
    rw [heq, integral_add (integrable_const _) (hMoment.1.const_mul C)]
    rw [integral_const_mul, hMoment.2]
    simp
  have hBound :
      (∫ ω, V (y + Z ω) ∂P) ≤ A + C := by
    calc
      _ ≤ (∫ ω, A + B * Real.exp (-phi * ((y + Z ω) - v)) ∂P) :=
        integral_mono hValueInt hSupportInt (fun ω => hMaj (y + Z ω))
      _ = A + C := hSupportIntegral
  have hNonneg : 0 ≤ (t : ℝ) := t.property
  have hDisc : Real.exp (-q * (t : ℝ)) ≤ 1 := by
    have hx : -q * (t : ℝ) ≤ 0 := by nlinarith [mul_nonneg hq hNonneg]
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr hx)
  have hCancel :
      Real.exp (-q * (t : ℝ)) * Real.exp (q * (t : ℝ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  calc
    Real.exp (-q * (t : ℝ)) * (∫ ω, V (y + Z ω) ∂P)
      ≤ Real.exp (-q * (t : ℝ)) * (A + C) :=
        mul_le_mul_of_nonneg_left hBound (Real.exp_nonneg _)
    _ = Real.exp (-q * (t : ℝ)) * A +
        (Real.exp (-q * (t : ℝ)) * Real.exp (q * (t : ℝ))) *
          (B * Real.exp (-phi * (y - v))) := by
          dsimp [C]
          ring
    _ = Real.exp (-q * (t : ℝ)) * A +
        B * Real.exp (-phi * (y - v)) := by rw [hCancel]; ring
    _ ≤ A + B * Real.exp (-phi * (y - v)) := by
          have hx := mul_le_mul_of_nonneg_right hDisc hA
          nlinarith
    _ = V y := hTouch.symm
