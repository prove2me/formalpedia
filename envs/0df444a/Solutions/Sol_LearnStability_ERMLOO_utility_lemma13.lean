-- Prove2me | solution 1 for LearnStability.ERMLOO.utility_lemma13
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T04:54:17.342735+00:00
-- url     : https://prove2.me/submissions/46c9b4fe-24c6-4a01-96ed-4cc8063c7388

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Integrable X μ) (hY : Integrable Y μ) (hXY : X ≤ᵐ[μ] Y) :
    ∫ ω, |X ω| ∂μ ≤ |∫ ω, X ω ∂μ| + 2 * ∫ ω, |Y ω| ∂μ := by
  have hXp : Integrable (fun ω => (X ω)⁺) μ := hX.pos_part
  have hXn : Integrable (fun ω => (X ω)⁻) μ := hX.neg_part
  have hYabs : Integrable (fun ω => |Y ω|) μ := hY.abs
  have hpt1 : ∀ x : ℝ, |x| = x + 2 * x⁻ := by
    intro x
    have h1 : x = x⁺ - x⁻ := (posPart_sub_negPart x).symm
    have h2 : |x| = x⁺ + x⁻ := (posPart_add_negPart x).symm
    linarith
  have hpt2 : ∀ x : ℝ, |x| = -x + 2 * x⁺ := by
    intro x
    have h1 : x = x⁺ - x⁻ := (posPart_sub_negPart x).symm
    have h2 : |x| = x⁺ + x⁻ := (posPart_add_negPart x).symm
    linarith
  have h_up : ∫ ω, (X ω)⁺ ∂μ ≤ ∫ ω, |Y ω| ∂μ := by
    refine integral_mono_ae hXp hYabs ?_
    filter_upwards [hXY] with ω hle
    exact sup_le (hle.trans (le_abs_self (Y ω))) (abs_nonneg (Y ω))
  have hXeq : ∫ ω, X ω ∂μ = ∫ ω, (X ω)⁺ ∂μ - ∫ ω, (X ω)⁻ ∂μ := by
    rw [← integral_sub hXp hXn]
    refine integral_congr_ae ?_
    filter_upwards with ω
    exact (posPart_sub_negPart (X ω)).symm
  rcases le_total 0 (∫ ω, X ω ∂μ) with hm | hm
  · have habs : ∫ ω, |X ω| ∂μ = ∫ ω, X ω ∂μ + 2 * ∫ ω, (X ω)⁻ ∂μ := by
      calc ∫ ω, |X ω| ∂μ = ∫ ω, (fun ω => X ω + 2 * (X ω)⁻) ω ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with ω
            exact hpt1 (X ω)
        _ = ∫ ω, X ω ∂μ + ∫ ω, (fun ω => 2 * (X ω)⁻) ω ∂μ :=
            integral_add hX (hXn.const_mul 2)
        _ = ∫ ω, X ω ∂μ + 2 * ∫ ω, (X ω)⁻ ∂μ := by rw [integral_const_mul]
    have hun : ∫ ω, (X ω)⁻ ∂μ ≤ ∫ ω, |Y ω| ∂μ := by
      have h : ∫ ω, (X ω)⁻ ∂μ = ∫ ω, (X ω)⁺ ∂μ - ∫ ω, X ω ∂μ := by linarith
      linarith [h, h_up]
    calc ∫ ω, |X ω| ∂μ = |∫ ω, X ω ∂μ| + 2 * ∫ ω, (X ω)⁻ ∂μ := by
          rw [habs, abs_of_nonneg hm]
      _ ≤ |∫ ω, X ω ∂μ| + 2 * ∫ ω, |Y ω| ∂μ := by linarith
  · have habs : ∫ ω, |X ω| ∂μ = -∫ ω, X ω ∂μ + 2 * ∫ ω, (X ω)⁺ ∂μ := by
      calc ∫ ω, |X ω| ∂μ = ∫ ω, (fun ω => -X ω + 2 * (X ω)⁺) ω ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with ω
            exact hpt2 (X ω)
        _ = ∫ ω, -X ω ∂μ + ∫ ω, (fun ω => 2 * (X ω)⁺) ω ∂μ :=
            integral_add hX.neg (hXp.const_mul 2)
        _ = -∫ ω, X ω ∂μ + 2 * ∫ ω, (X ω)⁺ ∂μ := by
            rw [integral_neg, integral_const_mul]
    calc ∫ ω, |X ω| ∂μ = |∫ ω, X ω ∂μ| + 2 * ∫ ω, (X ω)⁺ ∂μ := by
          rw [habs, abs_of_nonpos hm]
      _ ≤ |∫ ω, X ω ∂μ| + 2 * ∫ ω, |Y ω| ∂μ := by linarith
