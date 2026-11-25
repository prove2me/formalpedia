-- Prove2me | solution 1 for Kyprianou.Ch04.trafficIntegratedNegativeTailProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:09:32.912565+00:00
-- url     : https://prove2.me/submissions/7752bde4-7edb-4759-9f0b-2f5595c15b17

import Mathlib
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Inv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_original_negative_tail_unweighted_layercake
import Theorems.Thm_Kyprianou_Ch04_normalisedTailDensityIsProbability
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Normalised negative integrated Levy tail is a probability law in subcritical traffic. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let rho : ENNReal :=
      (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
      IsProbabilityMeasure
        (((volume : Measure ℝ).restrict (Ioi 0)).withDensity
          (fun x : ℝ =>
            L.ν (Iio (-x)) /
              (ENNReal.ofReal L.drift * rho))) := by
  intro rho hrho hrho1
  let D : ENNReal := ENNReal.ofReal L.drift
  let M : ENNReal := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
  have hD : D ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hd)
  have hDtop : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hRtop : rho ≠ ⊤ :=
    ne_of_lt (lt_trans hrho1 ENNReal.one_lt_top)
  have hMass : (∫⁻ x : ℝ, L.ν (Iio (-x))
      ∂((volume : Measure ℝ).restrict (Ioi 0))) = M := by
    exact (original_negative_tail_unweighted_layercake L.ν L.ν_Ici).symm
  have hEqual : M = D * rho := by
    change M = D * (M / D)
    exact (ENNReal.mul_div_cancel hD hDtop).symm
  have hAnti : Antitone (fun x : ℝ => L.ν (Iio (-x))) := by
    intro x y hxy
    apply measure_mono
    exact Iio_subset_Iio (neg_le_neg hxy)
  have hMeas : Measurable (fun x : ℝ => L.ν (Iio (-x))) :=
    hAnti.measurable
  have hKpos : 0 < D * rho := ENNReal.mul_pos hD (ne_of_gt hrho)
  have hKtop : D * rho ≠ ⊤ := by
    exact ENNReal.mul_ne_top hDtop hRtop
  exact Kyprianou.Ch04.normalisedTailDensityIsProbability
    ((volume : Measure ℝ).restrict (Ioi 0))
    (fun x : ℝ => L.ν (Iio (-x))) hMeas (D * rho)
    hKpos hKtop (hMass.trans hEqual)
