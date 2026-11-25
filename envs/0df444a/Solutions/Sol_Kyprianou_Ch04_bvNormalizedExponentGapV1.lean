-- Prove2me | solution 1 for Kyprianou.Ch04.bvNormalizedExponentGapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:15:48.632802+00:00
-- url     : https://prove2.me/submissions/adcdfc3e-79fc-4e36-9bfe-34ba827ba6ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_nonneg
import Theorems.Thm_AvramDividend_Classical_negative_jump_magnitude_integral_transform
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
open Set


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)

    (a : Real) (ha : 0 < a) :
    (∫⁻ y : Real, ENNReal.ofReal ((1 - Real.exp (a*y))/a) ∂L.ν) =
      ENNReal.ofReal ((L.drift*a - L.ψ a)/a) := by
  let mu := L.ν.restrict (Set.Iio (0 : Real))
  have hrestrict : (∫⁻ y : Real, ENNReal.ofReal ((1 - Real.exp (a*y))/a) ∂L.ν) =
      ∫⁻ y : Real, ENNReal.ofReal ((1 - Real.exp (a*y))/a) ∂mu := by
    rw [← lintegral_indicator measurableSet_Iio]
    apply lintegral_congr
    intro y
    by_cases hy : y < 0
    · simp [hy]
    · have hz : (1 - Real.exp (a*y))/a ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (Real.one_le_exp_iff.mpr (mul_nonneg ha.le (le_of_not_gt hy)))) ha.le
      simp [hy, ENNReal.ofReal_eq_zero.mpr hz]
  rw [hrestrict]
  have hpsi : L.ψ a = L.drift*a - ∫ y, 1 - Real.exp (a*y) ∂mu := by
    rw [bv_laplace_exponent_positive_magnitude_nonneg L hBV a ha.le,
      negative_jump_magnitude_integral_transform]
  have hi : Integrable (fun y => (1 - Real.exp (a*y))/a) mu := by
    convert ((bv_exponential_jump_integrable_nonneg L hBV a ha.le).neg.div_const a) using 1
    ext y; simp only [Pi.neg_apply]; ring
  have hn : ∀ᵐ y ∂mu, 0 ≤ (1 - Real.exp (a*y))/a := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_lt hy)))) ha.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div, hpsi]
  congr 2; ring
