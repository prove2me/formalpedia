-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_discount_series_laplace_positive_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:12:04.693367+00:00
-- url     : https://prove2.me/submissions/1e67f7a1-61c9-479d-a221-9425918cafb6

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_scaled_series_laplace
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 < q) (hβ : 0 ≤ β)
    (hroot0 : Phi ψ 0 < β) (hrootq : Phi ψ q < β) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
      (ψ β - q)⁻¹ := by
  have hgap := source_scale_laplace_gap_pos ψ W hW q β hq.le hβ hrootq
  have hψ : 0 < ψ β := lt_trans hq hgap
  have hden : 1 - q / ψ β ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr ((div_lt_one hψ).2 hgap))
  have hseries : ∀ x : ℝ,
      (∑' n : ℕ, q ^ (n + 1) * scaleConvolutionPower (W 0) n x) =
        q * (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) := by
    intro x
    calc
      (∑' n : ℕ, q ^ (n + 1) * scaleConvolutionPower (W 0) n x) =
          ∑' n : ℕ, q * (q ^ n * scaleConvolutionPower (W 0) n x) := by
            congr 1
            ext n
            rw [pow_succ]
            ring
      _ = q * (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) :=
        tsum_mul_left
  have hmass := source_scale_scaled_series_laplace ψ W hW q β hq.le hβ hroot0 hrootq
  have hint : q * (∫ x in Set.Ioi (0 : ℝ),
       Real.exp (-(β * x)) *
         (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
       (q / ψ β) / (1 - q / ψ β) := by
    calc
      q * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
         (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
       (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
         (∑' n : ℕ, q ^ (n+1) * scaleConvolutionPower (W 0) n x) ∂volume) := by
        simp_rw [hseries]
        have heq : (fun x : ℝ => Real.exp (-(β * x)) *
          (q * (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x))) =
          (fun x : ℝ => q * (Real.exp (-(β * x)) *
          (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x))) := by
          funext x
          ring
        rw [heq, integral_const_mul]
      _ = (q / ψ β) / (1 - q / ψ β) := hmass
  have hrat : (q / ψ β) / (1 - q / ψ β) =
      q * (ψ β - q)⁻¹ := by
    field_simp [ne_of_gt hψ, hden, ne_of_gt (sub_pos.mpr hgap)]
  apply mul_left_cancel₀ (ne_of_gt hq)
  exact hint.trans hrat
