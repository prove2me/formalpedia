-- Prove2me | solution 1 for GoldieRenewal.Implicit.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:35:13.139973+00:00
-- url     : https://prove2.me/submissions/ab50dfaa-af17-472b-9408-7f96a661b506

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
open MeasureTheory ProbabilityTheory
open scoped ENNReal


namespace GoldieRenewal.Implicit

lemma l22_rpow_eq (κ x : ℝ) (hx : x ≠ 0) : |x| ^ κ = Real.exp (κ * Real.log |x|) := by
  rw [Real.rpow_def_of_pos (abs_pos.2 hx), mul_comm]

lemma l22_good_pos (κ : ℝ) (ν : Measure ℝ) (hC : CramerConditions κ ν) :
    ν {x : ℝ | x ≠ 0 ∧ Real.log |x| ≠ 0} ≠ 0 := by
  intro h0
  apply hC.nonarithmetic
  refine ⟨1, one_pos, ?_⟩
  have hmeasS : MeasurableSet (Set.range (fun n : ℤ => (n : ℝ) * 1)) :=
    (Set.countable_range _).measurableSet
  have hg : Measurable (fun x : ℝ => Real.log |x|) := by fun_prop
  rw [Measure.map_apply hg hmeasS.compl]
  have hs : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton (0:ℝ)).compl
  rw [ProbabilityTheory.cond_apply hs]
  have : {x : ℝ | x ≠ 0} ∩ (fun x : ℝ => Real.log |x|) ⁻¹' (Set.range (fun n : ℤ => (n : ℝ) * 1))ᶜ
      ⊆ {x : ℝ | x ≠ 0 ∧ Real.log |x| ≠ 0} := by
    intro x ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    intro hl
    apply hx2
    simp only [Set.mem_preimage]
    exact ⟨0, by simp [hl]⟩
  rw [measure_mono_null this h0, mul_zero]

theorem lemma_2_2_core (ν : Measure ℝ) (κ : ℝ) (hC : CramerConditions κ ν) :
    (logPlusMoment ν < ∞ ∧ logAbsMean ν < 0) ∧
      (Integrable (fun x : ℝ => |x| ^ κ * Real.log |x|) ν ∧
        0 < cramerMean κ ν) := by
  haveI : IsProbabilityMeasure ν := ⟨hC.probability⟩
  have hκ := hC.pos
  have hgood := l22_good_pos κ ν hC
  -- measurability
  have hm1 : Measurable (fun x : ℝ => |x| ^ κ) := by fun_prop
  have hm2 : Measurable (fun x : ℝ => Real.log |x|) := by fun_prop
  have hm3 : Measurable (fun x : ℝ => |x| ^ κ * max (Real.log |x|) 0) := by fun_prop
  -- (2.6) part 1
  have hplus : logPlusMoment ν ≤ ∫⁻ x, ENNReal.ofReal (|x| ^ κ * max (Real.log |x|) 0) ∂ν := by
    unfold logPlusMoment
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    rcases le_or_gt (Real.log |x|) 0 with hl | hl
    · rw [max_eq_right hl]; positivity
    · rw [max_eq_left hl.le]
      have hx1 : 1 < |x| := by
        by_contra hc; push_neg at hc
        have := Real.log_nonpos (abs_nonneg x) hc
        linarith
      have : 1 ≤ |x| ^ κ := Real.one_le_rpow hx1.le hκ.le
      nlinarith
  have hplus_fin : logPlusMoment ν < ∞ := lt_of_le_of_lt hplus hC.moment_log_finite
  refine ⟨⟨hplus_fin, ?_⟩, ?_⟩
  · -- E log|M| < 0
    set Lm : ℝ → ℝ≥0∞ := fun x => if x = 0 then ∞ else ENNReal.ofReal (max (-Real.log |x|) 0)
      with hLm
    have hLm_meas : Measurable Lm := by
      apply Measurable.ite (measurableSet_singleton 0) measurable_const
      fun_prop
    set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal κ * ENNReal.ofReal (max (Real.log |x|) 0) + 1
      with hF
    set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (|x| ^ κ) + ENNReal.ofReal κ * Lm x with hG
    have hFint : ∫⁻ x, F x ∂ν = ENNReal.ofReal κ * logPlusMoment ν + 1 := by
      rw [hF, lintegral_add_right _ measurable_const, lintegral_const_mul _ (by fun_prop)]
      simp [logPlusMoment]
    have hGint : ∫⁻ x, G x ∂ν = 1 + ENNReal.ofReal κ * logMinusMoment ν := by
      rw [hG, lintegral_add_left (by fun_prop), lintegral_const_mul _ hLm_meas,
        hC.moment_eq_one]
      rfl
    have hFG : ∀ x, x ≠ 0 → Real.log |x| ≠ 0 → F x < G x := by
      intro x hx hl
      simp only [hF, hG, hLm, if_neg hx]
      rw [← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by positivity) zero_le_one,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), l22_rpow_eq κ x hx]
      have h1 := Real.add_one_lt_exp (x := κ * Real.log |x|) (mul_ne_zero hκ.ne' hl)
      rcases le_or_gt (Real.log |x|) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; nlinarith
      · rw [max_eq_left h.le, max_eq_right (by linarith)]; nlinarith
    have hFG' : ∀ x, F x ≤ G x := by
      intro x
      by_cases hx : x = 0
      · simp only [hG, hLm, if_pos hx]
        rw [ENNReal.mul_top (by simp [hκ])]; simp
      by_cases hl : Real.log |x| = 0
      · simp only [hF, hG, hLm, if_neg hx, hl]
        rw [l22_rpow_eq κ x hx, hl]; simp
      · exact (hFG x hx hl).le
    have hlt : ∫⁻ x, F x ∂ν < ∫⁻ x, G x ∂ν := by
      apply lintegral_strict_mono_of_ae_le_of_ae_lt_on (s := {x : ℝ | x ≠ 0 ∧ Real.log |x| ≠ 0})
        (by fun_prop) ?_ (Filter.Eventually.of_forall hFG') hgood
      · exact Filter.Eventually.of_forall (fun x hx => hFG x hx.1 hx.2)
      · rw [hFint]; exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hplus_fin.ne, by simp⟩
    rw [hFint, hGint, add_comm] at hlt
    have hlt2 : logPlusMoment ν < logMinusMoment ν := by
      by_contra hc; push_neg at hc
      have : 1 + ENNReal.ofReal κ * logMinusMoment ν ≤ 1 + ENNReal.ofReal κ * logPlusMoment ν := by
        gcongr
      exact absurd hlt (not_lt.2 this)
    unfold logAbsMean
    by_cases htop : logMinusMoment ν = ∞
    · rw [htop]
      have : (logPlusMoment ν : EReal) ≠ ⊤ := by simpa using hplus_fin.ne
      rw [EReal.coe_ennreal_top, EReal.sub_top]
      exact EReal.bot_lt_zero
    · rw [← ENNReal.ofReal_toReal hplus_fin.ne, ← ENNReal.ofReal_toReal htop]
      rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
        max_eq_left ENNReal.toReal_nonneg, max_eq_left ENNReal.toReal_nonneg]
      rw [← EReal.coe_sub, EReal.coe_neg']
      have := (ENNReal.toReal_lt_toReal hplus_fin.ne htop).2 hlt2
      linarith
  · -- (2.7)
    have hint1 : Integrable (fun x : ℝ => |x| ^ κ * max (Real.log |x|) 0) ν :=
      ⟨hm3.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall (fun x => by positivity))).2 hC.moment_log_finite⟩
    have hint0 : Integrable (fun x : ℝ => |x| ^ κ) ν :=
      ⟨hm1.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall (fun x => by positivity))).2 (by rw [hC.moment_eq_one]; simp)⟩
    have hmom : ∫ x, |x| ^ κ ∂ν = 1 := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => by positivity))
        hm1.aestronglyMeasurable, hC.moment_eq_one]; simp
    -- pointwise: κ y log y - y + 1 ≥ 0
    have hpt : ∀ x : ℝ, 0 ≤ κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ + 1 := by
      intro x
      by_cases hx : x = 0
      · subst hx; simp [Real.zero_rpow hκ.ne']
      · rw [l22_rpow_eq κ x hx]
        set s := κ * Real.log |x|
        have h1 := Real.add_one_le_exp (-s)
        have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
        have h3 := Real.exp_pos s
        nlinarith
    have hpt_pos : ∀ x : ℝ, x ≠ 0 → Real.log |x| ≠ 0 →
        0 < κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ + 1 := by
      intro x hx hl
      rw [l22_rpow_eq κ x hx]
      set s := κ * Real.log |x| with hs
      have hs0 : s ≠ 0 := mul_ne_zero hκ.ne' hl
      have h1 := Real.add_one_lt_exp (x := -s) (neg_ne_zero.2 hs0)
      have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
      have h3 := Real.exp_pos s
      nlinarith
    have hlow : ∀ x : ℝ, -(1/κ) ≤ |x| ^ κ * Real.log |x| := by
      intro x
      have h0 : 0 ≤ |x| ^ κ := by positivity
      have hA : -1 ≤ (|x| ^ κ * Real.log |x|) * κ := by nlinarith [hpt x]
      rw [neg_div', div_le_iff₀ hκ]; linarith
    have hint : Integrable (fun x : ℝ => |x| ^ κ * Real.log |x|) ν := by
      refine (hint1.add (integrable_const (1/κ))).mono' (by fun_prop) ?_
      filter_upwards with x
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_le]
      have h0 : 0 ≤ |x| ^ κ := by positivity
      have hk : 0 < 1/κ := by positivity
      constructor
      · have := hlow x
        have : 0 ≤ |x| ^ κ * max (Real.log |x|) 0 := by positivity
        linarith
      · have : |x| ^ κ * Real.log |x| ≤ |x| ^ κ * max (Real.log |x|) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) h0
        linarith
    refine ⟨hint, ?_⟩
    have hH : Integrable (fun x : ℝ => κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ + 1) ν :=
      ((hint.const_mul κ).sub hint0).add (integrable_const 1)
    have hpos : 0 < ∫ x, (κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ + 1) ∂ν := by
      rw [integral_pos_iff_support_of_nonneg hpt hH]
      refine lt_of_lt_of_le (pos_iff_ne_zero.2 hgood) (measure_mono ?_)
      intro x hx
      exact (hpt_pos x hx.1 hx.2).ne'
    have hA : Integrable (fun x : ℝ => κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ) ν :=
      (hint.const_mul κ).sub hint0
    have e1 : ∫ x, (κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ + 1) ∂ν =
        ∫ x, (κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ) ∂ν + ∫ _x, (1:ℝ) ∂ν :=
      integral_add hA (integrable_const 1)
    have e2 : ∫ x, (κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ) ∂ν =
        ∫ x, κ * (|x| ^ κ * Real.log |x|) ∂ν - ∫ x, |x| ^ κ ∂ν :=
      integral_sub (hint.const_mul κ) hint0
    have e3 : ∫ _x, (1:ℝ) ∂ν = 1 := by simp
    rw [e1, e2, integral_const_mul, hmom, e3] at hpos
    unfold cramerMean
    nlinarith

end GoldieRenewal.Implicit

open GoldieRenewal.Implicit


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (κ : ℝ) (hC : CramerConditions κ (P.map M)) :
    (logPlusMoment (P.map M) < ∞ ∧ logAbsMean (P.map M) < 0) ∧
      (Integrable (fun x : ℝ => |x| ^ κ * Real.log |x|) (P.map M) ∧
        0 < cramerMean κ (P.map M)) := by
  exact lemma_2_2_core (P.map M) κ hC
