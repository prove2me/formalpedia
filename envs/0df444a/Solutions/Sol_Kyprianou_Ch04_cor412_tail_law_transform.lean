-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_tail_law_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:41:03.769971+00:00
-- url     : https://prove2.me/submissions/240fdb29-8bc6-4287-96cb-ced2a7d3b545

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_integrated_tail_transform
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The reflected integrated-tail law has the same positive-ray exponential transform as the passage position. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (β : ℝ) (hβ : 0 < β) :
    let κ := (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/L.drift) * L.ν (Iio (-y)))
    (∫⁻ x, ENNReal.ofReal (Real.exp (β*x)) ∂(κ.map (fun y => -y))) =
      ENNReal.ofReal (1 - L.ψ β / (L.drift * β)) := by
  intro κ
  have ht : Measurable (fun y : ℝ => L.ν (Iio (-y))) := by
    apply Antitone.measurable
    intro x y hxy
    exact measure_mono (Iio_subset_Iio (neg_le_neg hxy))
  have hE : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-β*y))) := by fun_prop
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  change (∫⁻ y, ENNReal.ofReal (Real.exp (β * -y)) ∂κ) = _
  simp only [mul_neg, ← neg_mul] 
  change (∫⁻ y, ENNReal.ofReal (Real.exp (-β*y)) ∂
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/L.drift) * L.ν (Iio (-y)))) = _
  have hf : Measurable (fun y : ℝ => ENNReal.ofReal (1/L.drift) * L.ν (Iio (-y))) := measurable_const.mul ht
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hE]
  simp only [Pi.mul_apply, mul_assoc]
  have hg : Measurable (fun y : ℝ => L.ν (Iio (-y)) * ENNReal.ofReal (Real.exp (-β*y))) := ht.mul hE
  rw [lintegral_const_mul _ hg,
    Kyprianou.Ch04.cor412_integrated_tail_transform P F L hBV hd β hβ,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/L.drift)]
  congr 1
  field_simp [hd.ne', hβ.ne']
  <;> ring
