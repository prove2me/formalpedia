-- Prove2me | solution 1 for HlawkaGaussian.gauss_integral_scaling
-- status  : ACCEPTED   (prove)
-- author  : @sorry_not_sorry
-- created : 2026-10-08T06:36:41.940777+00:00
-- url     : https://prove2.me/submissions/1f976628-50e1-461c-88c1-7260804e896e

import Mathlib

open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Pushforward of the standard Gaussian along the inner-product functional:
`innerSL ℝ v` pushes `stdGaussian E` forward to `gaussianReal 0 ‖v‖²`.
This is `IsGaussian.map_eq_gaussianReal` applied to `stdGaussian E`:
the mean vanishes by `integral_strongDual_stdGaussian` and the variance is
`‖v‖²` by `variance_dual_stdGaussian` with `innerSL_apply_norm`. -/
theorem map_innerSL_stdGaussian (v : E) :
    (stdGaussian E).map (innerSL ℝ v)
      = gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  have h0 : IsGaussian (stdGaussian E) := inferInstance
  rw [h0.map_eq_gaussianReal (innerSL ℝ v), integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

/-- Gaussian integral representation of the norm: integrating `|⟪v, ·⟫|`
against the standard Gaussian recovers `‖v‖` up to the universal constant
`C = ∫ |s| ∂(gaussianReal 0 1)`. The proof pushes `stdGaussian E` forward
along `innerSL ℝ v` (change of variables), identifies the pushforward as
`gaussianReal 0 ‖v‖²`, and scales that down to `gaussianReal 0 1`.
(Uses `inner` rather than the `⟪·,·⟫_ℝ` notation, which needs a scope that
conflicts with the publish preamble.) -/
theorem solution (v : E) :
    ∫ w, |inner (𝕜 := ℝ) v w| ∂(stdGaussian E)
      = ‖v‖ * ∫ s, |s| ∂(gaussianReal 0 1) := by
  have hcoe : ∀ w : E, inner (𝕜 := ℝ) v w = ⇑(innerSL ℝ v) w := fun w => by simp
  have hscale : (gaussianReal 0 1).map (‖v‖ * ·)
      = gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · rw [mul_one, ← NNReal.coe_inj, NNReal.coe_mk,
        Real.coe_toNNReal _ (sq_nonneg _)]
  simp_rw [hcoe]
  rw [← integral_map (innerSL ℝ v).continuous.aemeasurable
    continuous_abs.aestronglyMeasurable, map_innerSL_stdGaussian, ← hscale,
    integral_map (measurable_const_mul _).aemeasurable
      continuous_abs.aestronglyMeasurable]
  have hfactor : ∀ s : ℝ, |‖v‖ * s| = ‖v‖ * |s| := fun s => by
    rw [abs_mul, abs_of_nonneg (norm_nonneg v)]
  simp_rw [hfactor]
  exact integral_const_mul ‖v‖ _
