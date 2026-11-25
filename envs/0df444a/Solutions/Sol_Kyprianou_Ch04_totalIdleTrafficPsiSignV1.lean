-- Prove2me | solution 1 for Kyprianou.Ch04.totalIdleTrafficPsiSignV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:15:39.788001+00:00
-- url     : https://prove2.me/submissions/dc15cd4d-4736-4443-873f-5c5ffe674191

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_bvNormalizedExponentGapV1
import Theorems.Thm_Kyprianou_Ch04_normalizedDeficitMomentCharacterisationV1
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_nonneg
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    : let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    (rho ≤ 1 ↔ ∀ theta : Real, 0 ≤ theta → 0 ≤ L.ψ theta) := by
  intro rho
  have ht : rho ≤ 1 ↔ (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) ≤ ENNReal.ofReal L.drift := by
    change _ / ENNReal.ofReal L.drift ≤ 1 ↔ _
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by positivity))
      (Or.inl ENNReal.ofReal_ne_top), one_mul]
  rw [ht, Kyprianou.Ch04.normalizedDeficitMomentCharacterisationV1]
  constructor
  · intro h a ha
    rcases ha.eq_or_lt with hz | hp
    · subst a
      have hzero := bv_laplace_exponent_positive_magnitude_nonneg L hBV 0 le_rfl
      rw [hzero]; simp
    have hb := h a hp
    rw [Kyprianou.Ch04.bvNormalizedExponentGapV1 P F L hBV hd a hp,
      ENNReal.ofReal_le_ofReal_iff hd.le, div_le_iff₀ hp] at hb
    linarith
  · intro h a ha
    rw [Kyprianou.Ch04.bvNormalizedExponentGapV1 P F L hBV hd a ha,
      ENNReal.ofReal_le_ofReal_iff hd.le, div_le_iff₀ ha]
    linarith [h a ha.le]
