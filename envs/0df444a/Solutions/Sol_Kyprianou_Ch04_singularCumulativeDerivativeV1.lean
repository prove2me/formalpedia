-- Prove2me | solution 1 for Kyprianou.Ch04.singularCumulativeDerivativeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:31:45.033831+00:00
-- url     : https://prove2.me/submissions/3b27a56e-d658-40ee-ad77-31ad597b987f

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- The cumulative mass of a finite singular measure has derivative zero almost everywhere. -/
theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ.MutuallySingular volume) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt (fun t : ℝ => (μ (Iic t)).toReal) 0 x := by
  by_cases hzero : μ = 0
  · subst μ
    exact Eventually.of_forall fun x => by
      simpa using (hasDerivAt_const x (0 : ℝ))
  let c := μ univ
  have hc0 : c ≠ 0 := fun h => hzero (Measure.measure_univ_eq_zero.mp h)
  have hcT : c ≠ ⊤ := (measure_lt_top μ univ).ne
  let ν : Measure ℝ := c⁻¹ • μ
  haveI : IsProbabilityMeasure ν := ⟨by
    simp [ν, c, Measure.smul_apply, ENNReal.inv_mul_cancel hc0 hcT]⟩
  have hs : ν.MutuallySingular volume := hμ.smul c⁻¹
  have hs' : (cdf ν).measure.MutuallySingular volume := by rwa [measure_cdf]
  have he : (fun t : ℝ => (μ (Iic t)).toReal) = fun t => c.toReal * cdf ν t := by
    funext t
    rw [cdf_eq_real, Measure.real_def]
    simp only [ν, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hcT⟩
    field_simp
  rw [he]
  filter_upwards [(cdf ν).ae_hasDerivAt, hs'.rnDeriv_ae_eq_zero] with x hx hz
  have h : HasDerivAt (cdf ν) 0 x := by simpa [hz] using hx
  simpa only [mul_zero] using h.const_mul c.toReal
