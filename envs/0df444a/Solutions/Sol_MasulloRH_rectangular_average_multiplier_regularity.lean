-- Prove2me | solution 1 for MasulloRH.rectangular_average_multiplier_regularity
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:15:57.057111+00:00
-- url     : https://prove2.me/submissions/dfd8d000-e1b3-40d8-a47a-ed60018c0443

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

open Filter MeasureTheory
open scoped Topology ENNReal

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (U V : ℕ → Set X) :
    let R := fun n => U n ×ˢ V n
    let ν := fun n => ((μ.prod μ) (R n))⁻¹ • (μ.prod μ).restrict (R n)
    ∀ (K q : X × X → ℂ) (q₀ : ℂ) (E : ℕ → ℝ) (C : ℝ),
    (∀ n, Integrable K (ν n)) →
    (∀ n, Integrable (fun x => q x * K x) (ν n)) →
    (∀ n, 0 ≤ E n) →
    (∀ n, ∀ᵐ x ∂ν n, ‖q x - q₀‖ ≤ E n) →
    (∀ n, ∫ x, ‖K x‖ ∂ν n ≤ C) → Tendsto E atTop (𝓝 0) →
    let A := fun n => ∫ x, K x ∂ν n
    let B := fun n => ∫ x, q x * K x ∂ν n
    (∀ n, ‖B n - q₀ * A n‖ ≤ E n * C) ∧
    Tendsto (fun n => B n - q₀ * A n) atTop (𝓝 0) ∧
    (∀ L : ℂ, q₀ ≠ 0 → (Tendsto (fun n => B n) atTop (𝓝 (q₀ * L)) ↔
      Tendsto (fun n => A n) atTop (𝓝 L))) := by
  intro R ν K q q₀ E C hK hqK hE hosc hbound hvan A B
  have bound (n : ℕ) : ‖B n - q₀ * A n‖ ≤ E n * C := by
    have hconst : Integrable (fun x => q₀ * K x) (ν n) := (hK n).const_mul _
    calc
      ‖B n - q₀ * A n‖ = ‖∫ x, (q x * K x - q₀ * K x) ∂ν n‖ := by
        rw [integral_sub (hqK n) hconst, integral_const_mul]
      _ ≤ ∫ x, ‖q x * K x - q₀ * K x‖ ∂ν n := norm_integral_le_integral_norm _
      _ ≤ ∫ x, E n * ‖K x‖ ∂ν n := by
        apply integral_mono_ae ((hqK n).sub hconst).norm ((hK n).norm.const_mul _)
        filter_upwards [hosc n] with x hx
        change ‖q x * K x - q₀ * K x‖ ≤ E n * ‖K x‖
        rw [← sub_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ = E n * ∫ x, ‖K x‖ ∂ν n := integral_const_mul _ _
      _ ≤ E n * C := mul_le_mul_of_nonneg_left (hbound n) (hE n)
  have err : Tendsto (fun n => B n - q₀ * A n) atTop (𝓝 0) := by
    apply squeeze_zero_norm bound
    simpa only [zero_mul] using hvan.mul_const C
  refine ⟨bound, err, ?_⟩
  intro L hq
  constructor
  · intro hb
    have scaled : Tendsto (fun n => q₀ * A n) atTop (𝓝 (q₀ * L)) := by
      simpa only [sub_sub_cancel, sub_zero] using hb.sub err
    simpa only [← mul_assoc, inv_mul_cancel₀ hq, one_mul] using scaled.const_mul q₀⁻¹
  · intro ha
    simpa only [sub_add_cancel, zero_add] using err.add (ha.const_mul q₀)
