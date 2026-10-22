-- Prove2me | solution 1 for JHolomorphic.eLpNorm_segment_average_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T20:16:17.696981+00:00
-- url     : https://prove2.me/submissions/8e270381-788a-49c7-954b-3db6ea907fcc

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_JHolomorphic_lintegral_ball_segment_le
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod



namespace JHolomorphic

open MeasureTheory Metric Filter
open scoped ENNReal

/-- The average of `G` over the segment `z + [0, 1] a` has `L^q(B(c, r))` norm at most the
`L^q(B(c, r + ‖a‖))` norm of `G`, for `1 ≤ q ≤ ∞`. -/
theorem eLpNorm_segment_average_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℂ → E} (hG : StronglyMeasurable G) {q : ℝ≥0∞} (hq : 1 ≤ q) (a c : ℂ) (r : ℝ) :
    eLpNorm (fun z => ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)) q (volume.restrict (ball c r)) ≤
      eLpNorm G q (volume.restrict (ball c (r + ‖a‖))) := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hν
  haveI : IsProbabilityMeasure ν := ⟨by simp [hν]⟩
  have hGm : Measurable fun x => ‖G x‖ₑ := hG.enorm
  have hF : ∀ z, (∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)) = ∫ t, G (z + (t:ℂ) * a) ∂ν := fun z =>
    intervalIntegral.integral_of_le zero_le_one
  have hsm : ∀ z, StronglyMeasurable fun t : ℝ => G (z + (t:ℂ) * a) := fun z =>
    hG.comp_measurable (measurable_const.add (Complex.measurable_ofReal.mul measurable_const))
  -- `‖F z‖ₑ ≤ ∫⁻ ‖G (z + t a)‖ₑ dν`
  have h1 : ∀ z, ‖∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)‖ₑ ≤
      eLpNorm (fun t : ℝ => G (z + (t:ℂ) * a)) 1 ν := by
    intro z
    rw [hF, eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_le_lintegral_enorm _
  have q0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  by_cases hqt : q = ⊤
  · subst hqt
    set M := eLpNorm G ⊤ (volume.restrict (ball c (r + ‖a‖)))
    set N := {w : ℂ | M < ‖G w‖ₑ}
    have hN : MeasurableSet N := measurableSet_lt measurable_const hGm
    have hN0 : ∫⁻ w in ball c (r + ‖a‖), N.indicator 1 w = 0 := by
      rw [lintegral_indicator_one hN, Measure.restrict_apply hN]
      have := ae_le_eLpNormEssSup (f := G) (μ := volume.restrict (ball c (r + ‖a‖)))
      rw [ae_iff, Measure.restrict_apply' measurableSet_ball] at this
      simpa [N, M, eLpNorm_exponent_top, not_le] using this
    have h2 := lintegral_ball_segment_le (N.indicator 1)
      (measurable_one.indicator hN) a c r
    rw [hN0, nonpos_iff_eq_zero, lintegral_eq_zero_iff] at h2
    swap
    · exact Measurable.lintegral_prod_right' (ν := ν)
        (f := fun p : ℂ × ℝ => N.indicator 1 (p.1 + (p.2:ℂ) * a))
        ((measurable_one.indicator hN).comp (measurable_fst.add
          ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const)))
    rw [eLpNorm_exponent_top, eLpNormEssSup]
    refine essSup_le_of_ae_le M ?_
    filter_upwards [h2] with z hz
    have hz' : ∀ᵐ t : ℝ ∂ν, N.indicator (1 : ℂ → ℝ≥0∞) (z + (t:ℂ) * a) = 0 := by
      have := (lintegral_eq_zero_iff ((measurable_one.indicator hN).comp
          (measurable_const.add (Complex.measurable_ofReal.mul measurable_const)))).1 hz
      filter_upwards [this] with t ht
      exact ht
    calc ‖∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)‖ₑ
        ≤ eLpNorm (fun t : ℝ => G (z + (t:ℂ) * a)) 1 ν := h1 z
      _ = ∫⁻ t, ‖G (z + (t:ℂ) * a)‖ₑ ∂ν := eLpNorm_one_eq_lintegral_enorm
      _ ≤ ∫⁻ _, M ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hz'] with t ht
          by_contra hlt
          have hmem : z + (t:ℂ) * a ∈ N := lt_of_not_ge hlt
          simp [Set.indicator_of_mem hmem] at ht
      _ = M := by simp
  · set p := q.toReal with hp
    have hp1 : 1 ≤ p := by simpa [hp] using ENNReal.toReal_mono hqt hq
    have hp0 : 0 < p := zero_lt_one.trans_le hp1
    have hpt : ∀ z, ‖∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)‖ₑ ^ p ≤
        ∫⁻ t, ‖G (z + (t:ℂ) * a)‖ₑ ^ p ∂ν := by
      intro z
      have h2 := eLpNorm_le_eLpNorm_of_exponent_le (μ := ν) hq (hsm z).aestronglyMeasurable
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal q0 hqt] at h2
      calc ‖∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)‖ₑ ^ p
          ≤ ((∫⁻ t, ‖G (z + (t:ℂ) * a)‖ₑ ^ p ∂ν) ^ (1 / p)) ^ p :=
            ENNReal.rpow_le_rpow ((h1 z).trans h2) hp0.le
        _ = ∫⁻ t, ‖G (z + (t:ℂ) * a)‖ₑ ^ p ∂ν := by
            rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal q0 hqt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal q0 hqt]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    calc ∫⁻ z in ball c r, ‖∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)‖ₑ ^ p
        ≤ ∫⁻ z in ball c r, ∫⁻ t in Set.Ioc (0:ℝ) 1, ‖G (z + (t:ℂ) * a)‖ₑ ^ p :=
          lintegral_mono fun z => hpt z
      _ ≤ ∫⁻ w in ball c (r + ‖a‖), ‖G w‖ₑ ^ p :=
          lintegral_ball_segment_le (fun w => ‖G w‖ₑ ^ p) (hGm.pow_const p) a c r

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℂ → E} (hG : StronglyMeasurable G) {q : ℝ≥0∞} (hq : 1 ≤ q) (a c : ℂ) (r : ℝ) :
    eLpNorm (fun z => ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)) q (volume.restrict (ball c r)) ≤
      eLpNorm G q (volume.restrict (ball c (r + ‖a‖))) :=
  eLpNorm_segment_average_le_aux hG hq a c r
