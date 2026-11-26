-- Prove2me | solution 1 for Kyprianou.Ch04.subcriticalZeroInitialWorkloadWeakLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:23.553493+00:00
-- url     : https://prove2.me/submissions/de92f322-925a-4599-b8ef-173e615b4127

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_subcriticalPathsBoundedBelowAE
import Theorems.Thm_Kyprianou_Ch04_measurableNegativeInfimumLimit
import Theorems.Thm_Kyprianou_Ch04_boundedContinuousExpectationTendsto
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedDrawdownInfimumLaw
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaMeasurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Weak convergence of zero-initial workload. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    ∃ mu : Measure ℝ, IsProbabilityMeasure mu ∧ mu (Iio 0) = 0 ∧
      (∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun t : NNReal => ∫ z, f (sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z) ∂P)
          atTop (nhds (∫ x, f x ∂mu))) := by
  intro M rho hr0 hr1
  let : IsProbabilityMeasure P := L.isProbability
  let D (t : NNReal) (z : Ω) := sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z
  let I (t : NNReal) (z : Ω) := -sInf ((fun s : NNReal => L.X s z) '' Iic t)
  have hb := Kyprianou.Ch04.subcriticalPathsBoundedBelowAE P F L hBV hd hr0 hr1
  obtain ⟨Z,hZm,hZ0,hZlim⟩ := Kyprianou.Ch04.measurableNegativeInfimumLimit P F L hb
  let nu := P.map Z
  have hnu : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map hZm.aemeasurable
  have hnu0 : nu (Iio 0) = 0 := by
    rw [show nu = P.map Z from rfl,Measure.map_apply hZm measurableSet_Iio]
    rw [ae_iff] at hZ0
    rw [show Z ⁻¹' Iio 0 = {z | ¬ 0 ≤ Z z} from by ext z; simp]
    exact hZ0
  have hI (t : NNReal) : Measurable (I t) :=
    (Kyprianou.Ch04.fixedHorizonSignedExtremaMeasurable P F L t).2.neg
  have hweak (f : BoundedContinuousFunction ℝ ℝ) :
      Tendsto (fun t : NNReal => ∫ z, f (D t z) ∂P)
        atTop (nhds (∫ x, f x ∂nu)) := by
    have h := Kyprianou.Ch04.boundedContinuousExpectationTendsto P I Z hI hZlim f
    rw [integral_map hZm.aemeasurable f.continuous.measurable.aestronglyMeasurable]
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : NNReal)] with t ht
    have he := (Kyprianou.Ch04.fixedHorizonSignedDrawdownInfimumLaw P F L t ht).comp
      (f.continuous.measurable.comp measurable_neg)
    simpa only [I,D,Function.comp_def,neg_sub] using he.integral_eq.symm
  exact ⟨nu,hnu,hnu0,hweak⟩
