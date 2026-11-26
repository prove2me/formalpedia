-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_integrated_tail_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:49:29.153792+00:00
-- url     : https://prove2.me/submissions/ce7e553c-89a1-4774-a7f1-c0d98c3fb506

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_discounted_positive_jump_tail_transform
import Theorems.Thm_Kyprianou_Ch04_bvNormalizedExponentGapV1
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (β : ℝ) (hβ : 0 < β) :
    (∫⁻ y in Ioi (0 : ℝ), L.ν (Iio (-y)) *
      ENNReal.ofReal (Real.exp (-β * y))) =
      ENNReal.ofReal ((L.drift * β - L.ψ β) / β) := by
  let f : ℝ → NNReal := fun z => Real.toNNReal (-z)
  have hf : Measurable f := by fun_prop
  let μ := L.ν.map f
  have ht := discounted_positive_jump_tail_transform μ β hβ
  have hl (y : ℝ) (hy : 0 < y) :
      μ {z : NNReal | y < (z : ℝ)} = L.ν (Iio (-y)) := by
    rw [Measure.map_apply hf (measurableSet_lt measurable_const (by fun_prop))]
    congr 1
    ext z
    change (y < ((Real.toNNReal (-z) : NNReal) : ℝ)) ↔ z < -y
    rw [Real.coe_toNNReal']
    rw [lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact (not_lt_of_ge hy.le h).elim
    · intro h
      exact Or.inl (by linarith)
  have hleft :
      (∫⁻ y in Ioi (0 : ℝ), L.ν (Iio (-y)) * ENNReal.ofReal (Real.exp (-β * y))) =
      ∫⁻ y in Ioi (0 : ℝ), μ {z : NNReal | y < (z : ℝ)} *
        ENNReal.ofReal (Real.exp (-β * y)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change L.ν (Iio (-y)) * _ = μ {z : NNReal | y < (z : ℝ)} * _
    rw [hl y hy]
  rw [hleft, ht]
  change (∫⁻ z : NNReal, ENNReal.ofReal ((1 - Real.exp (-β * (z : ℝ))) / β) ∂(L.ν.map f)) = _
  rw [lintegral_map (by fun_prop) hf]
  have hae : ∀ᵐ z ∂L.ν, z < 0 := by
    rw [ae_iff]
    simp only [not_lt]
    exact L.ν_Ici
  calc
    _ = ∫⁻ z : ℝ, ENNReal.ofReal ((1 - Real.exp (β * z)) / β) ∂L.ν := by
      apply lintegral_congr_ae
      filter_upwards [hae] with z hz
      change ENNReal.ofReal ((1 - Real.exp (-β * ((Real.toNNReal (-z) : NNReal) : ℝ))) / β) = _
      rw [Real.coe_toNNReal _ (neg_nonneg.mpr hz.le)]
      simp [neg_mul, mul_neg]
    _ = _ := Kyprianou.Ch04.bvNormalizedExponentGapV1 P F L hBV hd β hβ
