-- Prove2me | solution 1 for Kyprianou.Ch04.subcriticalInitialWorkloadLimitTransfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:01.254123+00:00
-- url     : https://prove2.me/submissions/65ec879e-dd73-47f0-8144-9ad67da6fb17

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_nonOverloadedPositiveLevelCrossingAE
import Theorems.Thm_Kyprianou_Ch04_boundedContinuousEventuallyEqualExpectations
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaMeasurable
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A fixed nonnegative initial workload preserves any limit of bounded continuous workload expectations. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    ∀ w : ℝ, 0 ≤ w → ∀ f : BoundedContinuousFunction ℝ ℝ, ∀ a : ℝ,
      Tendsto (fun t : NNReal => ∫ z, f (sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z) ∂P)
        atTop (nhds a) →
      Tendsto (fun t : NNReal => ∫ z, f (max w (sSup ((fun s : NNReal => L.X s z) '' Iic t)) - L.X t z) ∂P)
        atTop (nhds a) := by
  intro M rho hr0 hr1 w hw f a hlim
  let : IsProbabilityMeasure P := L.isProbability
  let S (t : NNReal) (z : Ω) := sSup ((fun s : NNReal => L.X s z) '' Iic t)
  let D (t : NNReal) (z : Ω) := S t z - L.X t z
  let W (t : NNReal) (z : Ω) := max w (S t z) - L.X t z
  have hD (t : NNReal) : Measurable (D t) := by
    have h := (Kyprianou.Ch04.fixedHorizonSignedExtremaMeasurable P F L t).1.neg
    change Measurable (fun z : Ω => -(L.X t z - S t z)) at h
    simpa only [neg_sub,D] using h
  have hW (t : NNReal) : Measurable (W t) := by
    have hx : Measurable (L.X t) := (L.adapted t).mono (F.le t) le_rfl
    have he : W t = fun z => max (w-L.X t z) (D t z) := by
      ext z
      exact (max_sub_sub_right _ _ _).symm
    rw [he]
    exact (measurable_const.sub hx).max (hD t)
  have hhit := Kyprianou.Ch04.nonOverloadedPositiveLevelCrossingAE P F L hBV hd
    hr1.le (w+1) (by linarith)
  have he : ∀ᵐ z ∂P, ∀ᶠ t in atTop, W t z = D t z := by
    filter_upwards [hhit] with z hz
    obtain ⟨t0,ht0⟩ := hz
    filter_upwards [eventually_ge_atTop t0] with t ht
    have hb := levyPath_bddAbove_Icc L z t
    have hset : Icc (0 : NNReal) t = Iic t := by ext x; simp
    rw [hset] at hb
    have hs : L.X t0 z ≤ S t z := le_csSup hb ⟨t0,ht,rfl⟩
    have hws : w ≤ S t z := by linarith
    simp only [W,D,max_eq_right hws]
  exact Kyprianou.Ch04.boundedContinuousEventuallyEqualExpectations P D W hD hW he f a hlim
