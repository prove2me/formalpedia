-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42ReflectedJumpMeasureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:52:31.565069+00:00
-- url     : https://prove2.me/submissions/f85d0e05-69c9-4dd3-a9fa-befdc5d68542

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_ae_positive
import Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_first_moment_integrable
open MeasureTheory Set AvramDividend.Classical Complex
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reflection of the negative jump measure supplies the subordinator exponent measure. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) :
    let ν := (L.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)
    Integrable (fun x : ℝ => min 1 |x|) (ν.restrict (Ioi 0)) ∧
      ∀ z : ℂ, (∫ x in Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν) =
        ∫ y in Iio (0 : ℝ), (1 - Complex.exp (z * (y : ℂ))) ∂L.ν := by
  dsimp only
  let ν := (L.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)
  have hp : ∀ᵐ x ∂ν, 0 < x := chat07_bv_neg_map_magnitude_ae_positive L
  have he : ν.restrict (Ioi 0) = ν := Measure.restrict_eq_self_of_ae_mem hp
  rw [show (L.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y) = ν from rfl, he]
  refine ⟨(chat07_bv_neg_map_magnitude_first_moment_integrable L hBV).congr ?_, ?_⟩
  · filter_upwards [hp] with x hx
    simp only [abs_of_pos hx]
  · intro z
    change (∫ x, (1 - Complex.exp (-z * (x : ℂ))) ∂ν) = _
    rw [show ν = (L.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y) from rfl,
      integral_map measurable_neg.aemeasurable (by fun_prop)]
    congr 1
    funext y
    push_cast
    rw [neg_mul_neg]
