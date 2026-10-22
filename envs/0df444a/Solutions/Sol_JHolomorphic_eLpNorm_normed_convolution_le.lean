-- Prove2me | solution 1 for JHolomorphic.eLpNorm_normed_convolution_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T17:30:57.302371+00:00
-- url     : https://prove2.me/submissions/3baf2104-c739-4575-85fd-1c2c40e0866b

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex



namespace JHolomorphic

open MeasureTheory Filter
open scoped Convolution ENNReal

/-- Mollification with a normed bump function does not increase `L^p` norms (`1 ≤ p < ∞`). -/
theorem eLpNorm_normed_convolution_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : ContDiffBump (0 : ℂ)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {g : ℂ → E}
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p volume ≤
      eLpNorm g p volume := by
  set w := ρ.normed volume with hw
  have hw0 : ∀ t, 0 ≤ w t := ρ.nonneg_normed
  have hwi : Integrable w := ρ.integrable_normed
  set ν := volume.withDensity (fun t => ENNReal.ofReal (w t)) with hν
  haveI : IsProbabilityMeasure ν := ⟨by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hwi (Eventually.of_forall hw0), hw,
      ρ.integral_normed, ENNReal.ofReal_one]⟩
  have hwm : Measurable fun t => ENNReal.ofReal (w t) :=
    ENNReal.measurable_ofReal.comp ρ.continuous_normed.measurable
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set r := p.toReal with hr
  have hr1 : 1 ≤ r := by
    have := ENNReal.toReal_mono hpt hp
    simpa [hr] using this
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  -- reduce to a strongly measurable representative
  suffices key : ∀ g' : ℂ → E, StronglyMeasurable g' →
      eLpNorm (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g') p volume ≤ eLpNorm g' p volume by
    have e1 : w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
        w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] hg.mk g :=
      convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ w) hg.ae_eq_mk
    have e2 : eLpNorm g p volume = eLpNorm (hg.mk g) p volume := eLpNorm_congr_ae hg.ae_eq_mk
    rw [e1, e2]
    exact key _ hg.stronglyMeasurable_mk
  intro g' hg'
  have hgm : Measurable fun x => ‖g' x‖ₑ := hg'.enorm
  -- pointwise Jensen bound
  have hpt' : ∀ x, ‖(w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g') x‖ₑ ^ r ≤
      ∫⁻ t, ‖g' (x - t)‖ₑ ^ r ∂ν := by
    intro x
    have hsm : StronglyMeasurable fun t => g' (x - t) :=
      hg'.comp_measurable (measurable_const.sub measurable_id)
    have hm : AEStronglyMeasurable (fun t => g' (x - t)) ν := hsm.aestronglyMeasurable
    have h1 : ‖(w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g') x‖ₑ ≤
        eLpNorm (fun t => g' (x - t)) 1 ν := by
      rw [eLpNorm_one_eq_lintegral_enorm, convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      rw [hν, lintegral_withDensity_eq_lintegral_mul₀ hwm.aemeasurable
        (show Measurable fun t => ‖g' (x - t)‖ₑ from
          hgm.comp (measurable_const.sub measurable_id)).aemeasurable]
      refine lintegral_congr fun t => ?_
      simp only [ContinuousLinearMap.lsmul_apply, enorm_smul, Pi.mul_apply, Function.comp_apply]
      rw [Real.enorm_eq_ofReal (hw0 t)]
    have h2 := eLpNorm_le_eLpNorm_of_exponent_le hp hm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt] at h2
    calc ‖(w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g') x‖ₑ ^ r
        ≤ ((∫⁻ t, ‖g' (x - t)‖ₑ ^ r ∂ν) ^ (1 / r)) ^ r :=
          ENNReal.rpow_le_rpow (h1.trans h2) hr0.le
      _ = ∫⁻ t, ‖g' (x - t)‖ₑ ^ r ∂ν := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hprod : AEMeasurable (Function.uncurry fun x t => ‖g' (x - t)‖ₑ ^ r)
      (volume.prod ν) :=
    ((hgm.pow_const r).comp (measurable_fst.sub measurable_snd)).aemeasurable
  calc ∫⁻ x, ‖(w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g') x‖ₑ ^ r
      ≤ ∫⁻ x, ∫⁻ t, ‖g' (x - t)‖ₑ ^ r ∂ν := lintegral_mono hpt'
    _ = ∫⁻ t, (∫⁻ x, ‖g' (x - t)‖ₑ ^ r) ∂ν := lintegral_lintegral_swap hprod
    _ = ∫⁻ t, (∫⁻ x, ‖g' x‖ₑ ^ r) ∂ν := by
        refine lintegral_congr fun t => ?_
        exact lintegral_sub_right_eq_self (fun x => ‖g' x‖ₑ ^ r) t
    _ = ∫⁻ x, ‖g' x‖ₑ ^ r := by rw [lintegral_const, measure_univ, mul_one]

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter
open scoped Convolution ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : ContDiffBump (0 : ℂ)) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {g : ℂ → E}
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p volume ≤
      eLpNorm g p volume :=
  JHolomorphic.eLpNorm_normed_convolution_le_aux ρ hp hpt hg
