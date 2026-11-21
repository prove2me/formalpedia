-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_scaled_series_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:21:47.206185+00:00
-- url     : https://prove2.me/submissions/ab77a47e-73fb-4bb9-aaa9-9be015440267

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_weighted_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_laplace_transform
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
import Theorems.Thm_AvramDividend_Classical_causal_geometric_laplace_resolvent_series
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hroot0 : Phi ψ 0 < β) (hrootq : Phi ψ q < β) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
      (∑' n : ℕ, q ^ (n + 1) *
        scaleConvolutionPower (W 0) n x) ∂volume) =
      (q / ψ β) / (1 - q / ψ β) := by
  have hgap := source_scale_laplace_gap_pos ψ W hW q β hq hβ hrootq
  have hψ : 0 < ψ β := lt_of_le_of_lt hq hgap
  have hρ0 : 0 ≤ q / ψ β := div_nonneg hq hψ.le
  have hρ1 : q / ψ β < 1 := (div_lt_one hψ).2 hgap
  let F : ℕ → ℝ → ℝ := fun n x =>
    q ^ (n + 1) * scaleConvolutionPower (W 0) n x
  have hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(β * x)) * F n x)
      (Set.Ioi (0 : ℝ)) volume := by
    intro n
    have hi := (source_scale_power_weighted_integrable ψ W hW β hβ hroot0) n
    have hi' : IntegrableOn
        (fun x : ℝ => Real.exp (-(β * x)) *
           scaleConvolutionPower (W 0) n x)
        (Set.Ioi (0 : ℝ)) volume := by
      simpa only [neg_mul] using hi
    have heq : (fun x : ℝ => Real.exp (-(β * x)) * F n x) =
        (fun x : ℝ => q ^ (n + 1) *
          (Real.exp (-(β * x)) * scaleConvolutionPower (W 0) n x)) := by
      funext x
      dsimp [F]
      ring
    rw [heq]
    exact hi'.const_mul _
  have hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x := by
    intro n x
    exact mul_nonneg (pow_nonneg hq _) ((source_scale_power_nonnegative_all_real ψ W hW) n x)
  have hmass : ∀ n : ℕ,
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) * F n x ∂volume) =
        (q / ψ β) ^ (n + 1) := by
    intro n
    have hpower := (source_scale_power_laplace_transform ψ W hW β hβ hroot0) n
    have hrewrite : (fun x : ℝ => Real.exp (-(β * x)) * F n x) =
        (fun x : ℝ => q ^ (n + 1) *
          (Real.exp (-(β * x)) * scaleConvolutionPower (W 0) n x)) := by
      funext x
      dsimp [F]
      ring
    rw [hrewrite, integral_const_mul]
    have hpower' :
        (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
          scaleConvolutionPower (W 0) n x ∂volume) =
        ((ψ β)⁻¹) ^ (n + 1) := by
      simpa only [neg_mul] using hpower
    rw [hpower']
    simp only [div_eq_mul_inv, mul_pow]
  have hmain := AvramDividend.Classical.causal_geometric_laplace_resolvent_series
    F β (q / ψ β) hρ0 hρ1 hFi hpos hmass
  simpa only [F] using hmain
