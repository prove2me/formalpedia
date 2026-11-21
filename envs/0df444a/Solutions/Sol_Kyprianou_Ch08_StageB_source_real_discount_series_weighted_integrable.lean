-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_real_discount_series_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:18:30.390306+00:00
-- url     : https://prove2.me/submissions/93da5d16-d2e5-4be2-933b-e54bfd7aaab3

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_weighted_series_terms_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_weighted_series_terms_pointwise_summable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_weighted_series_integral_masses_summable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x))
      (Set.Ioi (0 : ℝ)) volume := by
  let F : ℕ → ℝ → ℝ := fun n x => Real.exp (-(θ * x)) *
    (q ^ n * scaleConvolutionPower (W 0) n x)
  have hi := source_weighted_series_terms_integrable ψ W hW q θ hq hθ hroot0
  have hp := source_weighted_series_terms_pointwise_summable ψ W hW q θ hq
  have hm := source_weighted_series_integral_masses_summable
    ψ W hW q θ hq hθ hroot0 hrootq
  have hn : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x := by
    intro n x
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (pow_nonneg hq _)
        (source_scale_power_nonnegative_all_real ψ W hW n x))
  have h := AvramDividend.Classical.nonnegative_integrable_tsum_of_summable_integrals
    (volume.restrict (Set.Ioi (0 : ℝ))) F hi hn hp hm
  change Integrable (fun x : ℝ => Real.exp (-(θ * x)) *
    (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x))
    (volume.restrict (Set.Ioi (0 : ℝ)))
  have heq : (fun x : ℝ => Real.exp (-(θ * x)) *
    (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x)) =
    (fun x : ℝ => ∑' n : ℕ, F n x) := by
    funext x
    dsimp [F]
    rw [tsum_mul_left]
  rw [heq]
  exact h
