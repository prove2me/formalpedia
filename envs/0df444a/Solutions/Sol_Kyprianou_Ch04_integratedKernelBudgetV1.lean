-- Prove2me | solution 1 for Kyprianou.Ch04.integratedKernelBudgetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:46:47.53162+00:00
-- url     : https://prove2.me/submissions/4f5cd683-42dc-44cf-a67d-b811fc44e9a4

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Integrate a pointwise two-band square budget over marks, clock and samples. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) (T : NNReal)
    (H : ℝ → ℝ → Ω → ℝ) (S : Ω → ℝ) (A B : ℝ → ℝ)
    (hA : Integrable A ν) (hB : Integrable B ν) (hS : Integrable S P)
    (K : ℝ)
    (h : ∀ᵐ ω ∂P, ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), ∀ z : ℝ,
      (H s z ω)^2 ≤ K^2 * (A z + B z * S ω)) :
    (∫ ω, ∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ z, (H s z ω)^2 ∂ν ∂volume ∂P) ≤
      K^2 * (T : ℝ) * ((∫ z, A z ∂ν) + (∫ z, B z ∂ν) * ∫ ω, S ω ∂P) := by
  let a := ∫ z, A z ∂ν
  let b := ∫ z, B z ∂ν
  have hdom : Integrable (fun ω => (T : ℝ) * (K^2 * (a + b * S ω))) P :=
    ((integrable_const a).add (hS.const_mul b)).const_mul (K^2) |>.const_mul (T : ℝ)
  have hi (ω : Ω) (s : ℝ) (hs : ∀ z : ℝ,
      (H s z ω)^2 ≤ K^2 * (A z + B z * S ω)) :
      (∫ z, (H s z ω)^2 ∂ν) ≤ K^2 * (a + b * S ω) := by
    calc
      _ ≤ ∫ z, K^2 * (A z + B z * S ω) ∂ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          ((hA.add (hB.mul_const _)).const_mul _) (Eventually.of_forall hs)
      _ = _ := by
        rw [integral_const_mul, integral_add hA (hB.mul_const _), integral_mul_const]
  have htime : ∀ᵐ ω ∂P,
      (∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ z, (H s z ω)^2 ∂ν ∂volume) ≤
        (T : ℝ) * (K^2 * (a + b * S ω)) := by
    filter_upwards [h] with ω hω
    calc
      _ ≤ ∫ _ in Ioc (0 : ℝ) (T : ℝ), K^2 * (a + b * S ω) ∂volume :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
          (integrable_const _) ((ae_restrict_mem measurableSet_Ioc).mono
            (fun s hs => hi ω s (hω s hs)))
      _ = _ := by simp [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
        ENNReal.toReal_ofReal T.coe_nonneg, mul_comm]
  calc
    _ ≤ ∫ ω, (T : ℝ) * (K^2 * (a + b * S ω)) ∂P :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ =>
        integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _) hdom htime
    _ = _ := by
      rw [integral_const_mul, integral_const_mul, integral_add (integrable_const a)
        (hS.const_mul b), integral_const_mul]
      simp [integral_const, measureReal_def, a, b]
      <;> ring
