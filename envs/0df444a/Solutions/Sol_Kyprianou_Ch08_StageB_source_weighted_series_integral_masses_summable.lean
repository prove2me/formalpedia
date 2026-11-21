-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_weighted_series_integral_masses_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:18:16.237044+00:00
-- url     : https://prove2.me/submissions/164e5d06-671c-458a-8a68-4a15c94fd8fd

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_laplace_transform
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    Summable (fun n : ℕ =>
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) := by
  have hgap := source_scale_laplace_gap_pos ψ W hW q θ hq hθ hrootq
  have hψ : 0 < ψ θ := lt_of_le_of_lt hq hgap
  have hρ0 : 0 ≤ q / ψ θ := div_nonneg hq hψ.le
  have hρ1 : q / ψ θ < 1 := (div_lt_one hψ).2 hgap
  have hm : ∀ n : ℕ,
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
        (ψ θ)⁻¹ * (q / ψ θ)^n := by
    intro n
    have hp := (source_scale_power_laplace_transform ψ W hW θ hθ hroot0) n
    have hc : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        scaleConvolutionPower (W 0) n x ∂volume) =
        ((ψ θ)⁻¹)^(n+1) := by
      simpa only [neg_mul] using hp
    have heq : (fun x : ℝ => Real.exp (-(θ * x)) *
        (q ^ n * scaleConvolutionPower (W 0) n x)) =
        (fun x : ℝ => q ^ n * (Real.exp (-(θ * x)) *
          scaleConvolutionPower (W 0) n x)) := by
      funext x
      ring
    rw [heq, integral_const_mul, hc, pow_succ, div_eq_mul_inv, mul_pow]
    ring
  have hgeom : Summable (fun n : ℕ => (ψ θ)⁻¹ * (q / ψ θ)^n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left ((ψ θ)⁻¹)
  exact hgeom.congr (fun n => (hm n).symm)
