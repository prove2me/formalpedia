-- Prove2me | solution 1 for Kyprianou.Ch04.integratedNegativeTailLaplaceTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:23.491025+00:00
-- url     : https://prove2.me/submissions/a865ad15-0c9b-455a-bb50-c2c7750d4e79

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_negativeTailLaplaceLayercake
import Theorems.Thm_Kyprianou_Ch04_bvNormalizedExponentGapV1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The integrated-tail probability law has the normalized BV exponent deficit as its transform. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (r : ENNReal) (a : ℝ) (ha : 0 < a) :
    let eta := ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun x : ℝ => L.ν (Iio (-x)) / (ENNReal.ofReal L.drift * r))
    (∫⁻ x, ENNReal.ofReal (Real.exp (-a*x)) ∂eta) =
      (ENNReal.ofReal L.drift * r)⁻¹ *
        ENNReal.ofReal ((L.drift*a-L.ψ a)/a) := by
  intro eta
  let K := ENNReal.ofReal L.drift * r
  have hAnti : Antitone (fun x : ℝ => L.ν (Iio (-x))) := by
    intro x y hxy
    exact measure_mono (Iio_subset_Iio (neg_le_neg hxy))
  have hm : Measurable (fun x : ℝ => L.ν (Iio (-x)) / K) := hAnti.measurable.div_const K
  have he : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-a*x))) := by fun_prop
  change (∫⁻ x, ENNReal.ofReal (Real.exp (-a*x)) ∂
    (((volume : Measure ℝ).restrict (Ioi 0)).withDensity (fun x => L.ν (Iio (-x))/K))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hm he]
  simp only [Pi.mul_apply,div_eq_mul_inv,mul_assoc,mul_left_comm]
  calc
    _ = K⁻¹ * (∫⁻ x in Ioi (0 : ℝ), L.ν (Iio (-x)) * ENNReal.ofReal (Real.exp (-a*x))) :=
      lintegral_const_mul _ (hAnti.measurable.mul he)
    _ = _ := by
      rw [Kyprianou.Ch04.negativeTailLaplaceLayercake L.ν L.ν_Ici a ha,
        Kyprianou.Ch04.bvNormalizedExponentGapV1 P F L hBV hd a ha]
      rfl
