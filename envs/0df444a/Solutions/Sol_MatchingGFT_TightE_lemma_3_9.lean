-- Prove2me | solution 1 for MatchingGFT.TightE.lemma_3_9
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T19:31:09.348751+00:00
-- url     : https://prove2.me/submissions/f6c487fc-b0d6-43e4-a364-b08effc37745

import Mathlib

open MeasureTheory Set

namespace Lemma39Calc

/-- The weight `e^{-(1-h)} h 1{u ≤ e^{-h} t}` of the first term, as a function of `(h, u)`. -/
noncomputable def cfun (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(1 - p.1)) * p.1 * (if p.2 ≤ Real.exp (-p.1) * t then 1 else 0)

lemma measurable_cfun (t : ℝ) : Measurable (cfun t) := by
  unfold cfun
  refine ((Real.measurable_exp.comp (measurable_const.sub measurable_fst).neg).mul
    measurable_fst).mul ?_
  exact Measurable.ite (measurableSet_le measurable_snd
    ((Real.measurable_exp.comp measurable_fst.neg).mul measurable_const))
    measurable_const measurable_const

/-- `min(1, log(t/u))`. -/
noncomputable def mfun (t u : ℝ) : ℝ := min 1 (Real.log t - Real.log u)

/-- The weight `∫_0^{min(1, log(t/u))} h e^{h-1} dh`. -/
noncomputable def Wfun (t u : ℝ) : ℝ :=
  (mfun t u - 1) * Real.exp (-(1 - mfun t u)) + Real.exp (-1)

/-- The integrand of the second term after the substitution `u = e^{-h} t`. -/
noncomputable def gfun (Q : ℝ → ℝ) (t u : ℝ) : ℝ :=
  Real.exp (-(1 - Real.log (t / u))) * (1 - Real.log (t / u)) * Q u

lemma measurable_mfun (t : ℝ) : Measurable (mfun t) :=
  measurable_const.min (measurable_const.sub Real.measurable_log)

lemma measurable_Wfun (t : ℝ) : Measurable (Wfun t) := by
  unfold Wfun
  exact (((measurable_mfun t).sub measurable_const).mul
    (Real.measurable_exp.comp (measurable_const.sub (measurable_mfun t)).neg)).add measurable_const

lemma cond_iff {t u h : ℝ} (ht : 0 < t) (hu : 0 < u) :
    u ≤ Real.exp (-h) * t ↔ h ≤ Real.log t - Real.log u := by
  rw [← Real.log_le_log_iff hu (mul_pos (Real.exp_pos _) ht),
    Real.log_mul (Real.exp_pos _).ne' ht.ne', Real.log_exp]
  constructor <;> intro H <;> linarith

lemma mem_iff {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Real.exp (-1) * t ≤ u ↔ Real.log t - Real.log u ≤ 1 := by
  rw [← Real.log_le_log_iff (mul_pos (Real.exp_pos _) ht) hu,
    Real.log_mul (Real.exp_pos _).ne' ht.ne', Real.log_exp]
  constructor <;> intro H <;> linarith

lemma inner_h {t u : ℝ} (ht : 0 < t) (hu : u ∈ Ioc 0 t) :
    ∫ h in Ioc 0 1, cfun t (h, u) = Wfun t u := by
  have hH : 0 ≤ Real.log t - Real.log u := by
    have := Real.log_le_log hu.1 hu.2; linarith
  have e1 : (fun h => cfun t (h, u)) =
      (Iic (Real.log t - Real.log u)).indicator (fun h => Real.exp (-(1 - h)) * h) := by
    ext h
    simp only [cfun, indicator, mem_Iic]
    by_cases hc : h ≤ Real.log t - Real.log u
    · rw [if_pos ((cond_iff ht hu.1).mpr hc), if_pos hc, mul_one]
    · rw [if_neg (fun h' => hc ((cond_iff ht hu.1).mp h')), if_neg hc, mul_zero]
  have hset : Ioc (0 : ℝ) 1 ∩ Iic (Real.log t - Real.log u) =
      Ioc 0 (min 1 (Real.log t - Real.log u)) := by
    ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iic, le_min_iff]; tauto
  rw [e1, setIntegral_indicator measurableSet_Iic, hset,
    ← intervalIntegral.integral_of_le (le_min zero_le_one hH)]
  have hd : ∀ x, HasDerivAt (fun h => (h - 1) * Real.exp (-(1 - h)))
      (Real.exp (-(1 - x)) * x) x := by
    intro x
    have := ((hasDerivAt_id x).sub_const 1).mul ((hasDerivAt_id x).const_sub 1).neg.exp
    exact this.congr_deriv (by (try simp only [id, Pi.neg_apply, id_eq]); ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun x => Real.exp (-(1 - x)) * x).intervalIntegrable _ _)]
  simp only [Wfun, mfun, sub_zero, zero_sub]
  ring

lemma main_pos (Q : ℝ → ℝ) (hint : IntegrableOn Q (Ioo 0 1)) (t : ℝ) (ht0 : 0 < t)
    (ht1 : t ≤ 1) :
    ∫ h in (0 : ℝ)..1, Real.exp (-(1 - h)) *
        (h * (∫ u in (0 : ℝ)..(Real.exp (-h) * t), Q u) +
          (1 - h) * ((Real.exp (-h) * t) * Q (Real.exp (-h) * t))) =
      (1 / Real.exp 1) * ∫ u in (0 : ℝ)..t, Q u := by
  have hQt : IntegrableOn Q (Ioc 0 t) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr (hint.mono_set (Ioo_subset_Ioo_right ht1))
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  -- the first term as a double integral
  have hprod : Integrable (fun p : ℝ × ℝ => cfun t p * Q p.2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 t))) := by
    refine Integrable.bdd_mul (c := 1) (hQt.comp_snd _) (measurable_cfun t).aestronglyMeasurable ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := volume.restrict (Ioc 0 t))).ae (ae_restrict_mem measurableSet_Ioc)] with p hp
    have h1 : Real.exp (-(1 - p.1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hp.2])
    simp only [cfun, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hp.1]
    have h3 : |(if p.2 ≤ Real.exp (-p.1) * t then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> simp
    have := mul_le_mul (mul_le_mul h1 hp.2 hp.1.le zero_le_one) h3 (abs_nonneg _) (by norm_num)
    linarith
  have hAeq : ∀ h ∈ Ioc (0 : ℝ) 1,
      Real.exp (-(1 - h)) * (h * ∫ u in (0 : ℝ)..(Real.exp (-h) * t), Q u) =
        ∫ u in Ioc 0 t, cfun t (h, u) * Q u := by
    intro h hh
    have hφ0 : 0 ≤ Real.exp (-h) * t := (mul_pos (Real.exp_pos _) ht0).le
    have hφt : Real.exp (-h) * t ≤ t := by
      have : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hh.1])
      nlinarith
    rw [intervalIntegral.integral_of_le hφ0]
    have hset : Ioc 0 (Real.exp (-h) * t) = Ioc 0 t ∩ Iic (Real.exp (-h) * t) := by
      ext x; simp only [mem_Ioc, mem_inter_iff, mem_Iic]; constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hφt⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    rw [hset, ← setIntegral_indicator measurableSet_Iic, ← integral_const_mul,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    simp only [cfun, indicator, mem_Iic]
    split_ifs <;> ring
  have hAint : IntervalIntegrable (fun h => Real.exp (-(1 - h)) *
      (h * ∫ u in (0 : ℝ)..(Real.exp (-h) * t), Q u)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact IntegrableOn.congr_fun hprod.integral_prod_left (fun h hh => (hAeq h hh).symm) measurableSet_Ioc
  have hA : ∫ h in (0 : ℝ)..1, Real.exp (-(1 - h)) *
      (h * ∫ u in (0 : ℝ)..(Real.exp (-h) * t), Q u) = ∫ u in Ioc 0 t, Wfun t u * Q u := by
    rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_congr_fun measurableSet_Ioc hAeq]
    have hsw := integral_integral_swap (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := volume.restrict (Ioc 0 t)) (f := fun h u => cfun t (h, u) * Q u) hprod
    rw [hsw]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    (try simp only)
    rw [integral_mul_const, inner_h ht0 hu]
  -- the second term by the substitution `u = e^{-h} t`
  have ha0 : 0 < Real.exp (-1) * t := mul_pos (Real.exp_pos _) ht0
  have himg : (fun h => Real.exp (-h) * t) '' Icc 0 1 = Icc (Real.exp (-1) * t) t := by
    ext u; constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hh.2])) ht0.le, ?_⟩
      have : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hh.1])
      nlinarith
    · intro hu
      have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
      refine ⟨Real.log t - Real.log u, ⟨?_, (mem_iff ht0 hu0).mp hu.1⟩, ?_⟩
      · have := Real.log_le_log hu0 hu.2; linarith
      · simp only
        rw [neg_sub, Real.exp_sub, Real.exp_log hu0, Real.exp_log ht0]
        field_simp
  have hderiv : ∀ h ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun h => Real.exp (-h) * t)
      (-(Real.exp (-h) * t)) (Icc 0 1) h := by
    intro h _
    have := ((hasDerivAt_id h).neg.exp).mul_const t
    exact (this.congr_deriv (by (try simp only [id, Pi.neg_apply, id_eq]); ring)).hasDerivWithinAt
  have hinj : InjOn (fun h => Real.exp (-h) * t) (Icc 0 1) := by
    intro x _ y _ hxy
    simp only at hxy
    have := Real.exp_injective (mul_right_cancel₀ ht0.ne' hxy)
    linarith
  have hgint : IntegrableOn (gfun Q t) (Icc (Real.exp (-1) * t) t) := by
    have hQa : IntegrableOn Q (Icc (Real.exp (-1) * t) t) := hQt.mono_set (Icc_subset_Ioc ha0 le_rfl)
    unfold gfun
    have hml : Measurable fun u : ℝ => Real.log (t / u) :=
      Real.measurable_log.comp (measurable_const.div measurable_id)
    refine Integrable.bdd_mul (c := 1) hQa
      (((Real.measurable_exp.comp (measurable_const.sub hml).neg).mul
        (measurable_const.sub hml)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
    have hL0 : 0 ≤ Real.log (t / u) := Real.log_nonneg ((one_le_div hu0).mpr hu.2)
    have hL1 : Real.log (t / u) ≤ 1 := by
      rw [Real.log_div ht0.ne' hu0.ne']; exact (mem_iff ht0 hu0).mp hu.1
    have hE : Real.exp (-(1 - Real.log (t / u))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))]
    nlinarith [Real.exp_pos (-(1 - Real.log (t / u)))]
  have hBeqfun : ∀ h ∈ Icc (0 : ℝ) 1, |-(Real.exp (-h) * t)| • gfun Q t (Real.exp (-h) * t) =
      Real.exp (-(1 - h)) * ((1 - h) * ((Real.exp (-h) * t) * Q (Real.exp (-h) * t))) := by
    intro h _
    have hl : Real.log (t / (Real.exp (-h) * t)) = h := by
      rw [show t / (Real.exp (-h) * t) = Real.exp h by rw [Real.exp_neg]; field_simp]
      exact Real.log_exp h
    rw [abs_neg, abs_of_pos (mul_pos (Real.exp_pos _) ht0), smul_eq_mul, gfun, hl]
    ring
  have hBint : IntervalIntegrable (fun h => Real.exp (-(1 - h)) *
      ((1 - h) * ((Real.exp (-h) * t) * Q (Real.exp (-h) * t)))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hderiv hinj
      (gfun Q t)).mp (by rw [himg]; exact hgint)
    exact this.congr_fun hBeqfun measurableSet_Icc
  have hB : ∫ h in (0 : ℝ)..1, Real.exp (-(1 - h)) *
      ((1 - h) * ((Real.exp (-h) * t) * Q (Real.exp (-h) * t))) =
        ∫ u in Ioc 0 t, (Icc (Real.exp (-1) * t) t).indicator (gfun Q t) u := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      ← setIntegral_congr_fun measurableSet_Icc hBeqfun,
      ← integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj, himg,
      setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr (Icc_subset_Ioc ha0 le_rfl)]
  -- combine
  have hWint : IntegrableOn (fun u => Wfun t u * Q u) (Ioc 0 t) := by
    refine Integrable.bdd_mul (c := 1) hQt (measurable_Wfun t).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun u hu => ?_)
    have hH : 0 ≤ Real.log t - Real.log u := by
      have := Real.log_le_log hu.1 hu.2; linarith
    have hm0 : 0 ≤ mfun t u := le_min zero_le_one hH
    have hm1 : mfun t u ≤ 1 := min_le_left _ _
    have hE0 := Real.exp_pos (-(1 - mfun t u))
    have hE1 : Real.exp (-(1 - mfun t u)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have he0 := Real.exp_pos (-1)
    have he1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    rw [Real.norm_eq_abs, Wfun, abs_le]
    constructor
    · nlinarith [mul_nonneg hm0 hE0.le]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hE0.le]
  have hIint : IntegrableOn ((Icc (Real.exp (-1) * t) t).indicator (gfun Q t)) (Ioc 0 t) :=
    (hgint.integrable_indicator measurableSet_Icc).integrableOn
  have hsplit : ∫ h in (0 : ℝ)..1, Real.exp (-(1 - h)) *
        (h * (∫ u in (0 : ℝ)..(Real.exp (-h) * t), Q u) +
          (1 - h) * ((Real.exp (-h) * t) * Q (Real.exp (-h) * t))) =
      (∫ h in (0 : ℝ)..1, Real.exp (-(1 - h)) *
        (h * ∫ u in (0 : ℝ)..(Real.exp (-h) * t), Q u)) +
      ∫ h in (0 : ℝ)..1, Real.exp (-(1 - h)) *
        ((1 - h) * ((Real.exp (-h) * t) * Q (Real.exp (-h) * t))) := by
    rw [← intervalIntegral.integral_add hAint hBint]
    congr 1; ext h; ring
  rw [hsplit, hA, hB, ← integral_add hWint hIint, intervalIntegral.integral_of_le ht0.le,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
  have hu0 := hu.1
  have hlog : Real.log (t / u) = Real.log t - Real.log u := Real.log_div ht0.ne' hu0.ne'
  have he : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  simp only [Wfun, mfun, indicator_apply, gfun, hlog]
  by_cases hH : Real.log t - Real.log u ≤ 1
  · rw [min_eq_right hH, if_pos ⟨(mem_iff ht0 hu0).mpr hH, hu.2⟩, he]; ring
  · push_neg at hH
    rw [min_eq_left hH.le, if_neg (fun hm => by linarith [(mem_iff ht0 hu0).mp hm.1]), he]; ring

end Lemma39Calc

open Lemma39Calc in
theorem solution (Q : ℝ → ℝ) (hQ : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ Q u)
    (hint : IntegrableOn Q (Ioo 0 1)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ h in (0 : ℝ)..1, Real.exp (-(1 - h)) *
        (h * (∫ u in (0 : ℝ)..(Real.exp (-h) * t), Q u) +
          (1 - h) * ((Real.exp (-h) * t) * Q (Real.exp (-h) * t))) =
      (1 / Real.exp 1) * ∫ u in (0 : ℝ)..t, Q u := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0; simp
  · exact main_pos Q hint t h0 ht.2
