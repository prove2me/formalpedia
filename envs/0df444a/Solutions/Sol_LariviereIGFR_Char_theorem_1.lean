-- Prove2me | solution 1 for LariviereIGFR.Char.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T06:09:09.50321+00:00
-- url     : https://prove2.me/submissions/4fec123a-7039-4bac-a504-3f533bddd26f

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting
open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Set Filter LariviereIGFR.Char

namespace IGFRProof
end IGFRProof

open scoped Topology Classical
open MeasureTheory ProbabilityTheory Set Filter LariviereIGFR.Char

namespace IGFRProof

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {φ : ℝ → ℝ}

omit [IsProbabilityMeasure μ] in
theorem density_singleton (hφ : IsRegDensity μ φ) (x : ℝ) : μ {x} = 0 := by
  rw [hφ.2.1]
  exact measure_singleton x

omit [IsProbabilityMeasure μ] in
theorem measure_nonpositive (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    μ (Iic 0) = 0 := by
  rw [← Iio_union_right, measure_union (by simp) (measurableSet_singleton 0),
    hnn, density_singleton hφ, add_zero]

omit [IsProbabilityMeasure μ] in
theorem ae_positive (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    ∀ᵐ x ∂μ, 0 < x := by
  rw [ae_iff]
  simpa only [not_lt, Set.Iic] using measure_nonpositive hnn hφ

theorem cdf_zero_of_nonpos (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ)
    {x : ℝ} (hx : x ≤ 0) : cdf μ x = 0 := by
  rw [cdf_eq_real, measureReal_def]
  have h : μ (Iic x) = 0 := measure_mono_null (Iic_subset_Iic.mpr hx)
    (measure_nonpositive hnn hφ)
  rw [h, ENNReal.toReal_zero]

theorem density_zero_of_nonpos (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ)
    {x : ℝ} (hx : x ≤ 0) : φ x = 0 :=
  hφ.2.2.2 x (cdf_zero_of_nonpos hnn hφ hx)

theorem cdf_continuous (hφ : IsRegDensity μ φ) : Continuous (cdf μ : ℝ → ℝ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  have hs := (cdf μ).measure_singleton x
  rw [measure_cdf, density_singleton hφ] at hs
  have hle : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hs.symm
  exact le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) (by linarith)

theorem cdf_log_map (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ) (t : ℝ) :
    cdf (μ.map Real.log) t = cdf μ (Real.exp t) := by
  let : IsProbabilityMeasure (μ.map Real.log) :=
    μ.isProbabilityMeasure_map Real.measurable_log.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply Real.measurable_log measurableSet_Iic]
  congr 1
  apply measure_congr
  filter_upwards [ae_positive hnn hφ] with x hx
  exact propext (Real.log_le_iff_le_exp hx)

theorem cdf_scale_map {c : ℝ} (hc : 0 < c) (t : ℝ) :
    cdf (μ.map (fun x => c * x)) t = cdf μ (t / c) := by
  have hm : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  let : IsProbabilityMeasure (μ.map (fun x => c * x)) :=
    μ.isProbabilityMeasure_map hm.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply hm measurableSet_Iic]
  congr 2
  ext x
  simp only [mem_preimage, mem_Iic]
  rw [le_div_iff₀ hc, mul_comm]

theorem gen_zero_of_nonpos (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ)
    {x : ℝ} (hx : x ≤ 0) : genFailureRate μ φ x = 0 := by
  simp [genFailureRate, failureRate, density_zero_of_nonpos hnn hφ hx]

theorem gen_nonneg (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ) (x : ℝ) :
    0 ≤ genFailureRate μ φ x := by
  by_cases hx : x ≤ 0
  · rw [gen_zero_of_nonpos hnn hφ hx]
  · exact mul_nonneg (le_of_not_ge hx) (div_nonneg (hφ.1 x)
      (sub_nonneg.mpr (cdf_le_one μ x)))

end IGFRProof

open scoped Topology Classical
open MeasureTheory ProbabilityTheory Set Filter LariviereIGFR.Char

namespace IGFRProof

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {φ : ℝ → ℝ}

theorem log_rate (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ) (t : ℝ) :
    failureRate (μ.map Real.log) (fun t => Real.exp t * φ (Real.exp t)) t =
      genFailureRate μ φ (Real.exp t) := by
  simp only [failureRate, survival, cdf_log_map hnn hφ, genFailureRate]
  ring

theorem igfr_iff_log_ifr (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    IsIGFR μ φ ↔ IsIFR (μ.map Real.log) (fun t => Real.exp t * φ (Real.exp t)) := by
  constructor
  · intro h a ha b hb hab
    rw [log_rate hnn hφ, log_rate hnn hφ]
    apply h
    · simpa only [mem_ofPred_eq, cdf_log_map hnn hφ] using ha
    · simpa only [mem_ofPred_eq, cdf_log_map hnn hφ] using hb
    · exact Real.exp_le_exp.mpr hab
  · intro h a ha b hb hab
    by_cases haz : a ≤ 0
    · rw [gen_zero_of_nonpos hnn hφ haz]
      exact gen_nonneg hnn hφ b
    · have ha0 : 0 < a := lt_of_not_ge haz
      have hb0 : 0 < b := ha0.trans_le hab
      have hr := h (a := Real.log a) (by simpa [cdf_log_map hnn hφ, Real.exp_log ha0] using ha)
        (b := Real.log b) (by simpa [cdf_log_map hnn hφ, Real.exp_log hb0] using hb)
        (Real.log_le_log ha0 hab)
      simpa only [log_rate hnn hφ, Real.exp_log ha0, Real.exp_log hb0] using hr

theorem scaled_rate {c : ℝ} (hc : 0 < c) (x : ℝ) :
    failureRate (μ.map (fun y => c * y)) (fun y => φ (y / c) / c) x =
      failureRate μ φ (x / c) / c := by
  simp only [failureRate, survival, cdf_scale_map hc]
  ring

theorem igfr_iff_scale (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    IsIGFR μ φ ↔ ∀ c : ℝ, 1 ≤ c →
      HazardRateLE μ φ (μ.map (fun x => c * x)) (fun x => φ (x / c) / c) := by
  constructor
  · intro h c hc x hx hxc
    have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
    rw [scaled_rate hc0]
    rcases hx.eq_or_lt with hx | hx
    · subst x
      simp [failureRate, density_zero_of_nonpos hnn hφ le_rfl]
    · have hdiv : x / c ≤ x := (div_le_self (le_of_lt hx) hc)
      have hi := h (a := x / c) (lt_of_le_of_lt ((monotone_cdf μ) hdiv) hxc)
        (b := x) hxc hdiv
      dsimp [genFailureRate] at hi
      apply (mul_le_mul_iff_right₀ hx).mp
      convert hi using 1
      ring
  · intro h a ha b hb hab
    by_cases haz : a ≤ 0
    · rw [gen_zero_of_nonpos hnn hφ haz]
      exact gen_nonneg hnn hφ b
    · have ha0 : 0 < a := lt_of_not_ge haz
      have hb0 : 0 < b := ha0.trans_le hab
      have hc : 1 ≤ b / a := (le_div_iff₀ ha0).mpr (by simpa using hab)
      have hr := h (b / a) hc b hb0.le hb
      rw [scaled_rate (div_pos hb0 ha0)] at hr
      have hba : b / (b / a) = a := by field_simp
      rw [hba] at hr
      have hp := mul_le_mul_of_nonneg_right hr hb0.le
      dsimp [genFailureRate]
      convert hp using 1 <;> field_simp

noncomputable def logSurvival (μ : Measure ℝ) (t : ℝ) : ℝ := survival μ (Real.exp t)
noncomputable def logRate (μ : Measure ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  genFailureRate μ φ (Real.exp t)

theorem logSurvival_continuous (hφ : IsRegDensity μ φ) : Continuous (logSurvival μ) :=
  continuous_const.sub ((cdf_continuous hφ).comp Real.continuous_exp)

omit [IsProbabilityMeasure μ] in
theorem logSurvival_antitone : Antitone (logSurvival μ) := by
  intro a b hab
  exact sub_le_sub_left ((monotone_cdf μ) (Real.exp_le_exp.mpr hab)) 1

omit [IsProbabilityMeasure μ] in
theorem logSurvival_nonneg (t : ℝ) : 0 ≤ logSurvival μ t :=
  sub_nonneg.mpr (cdf_le_one μ _)

omit [IsProbabilityMeasure μ] in
theorem logSurvival_le_one (t : ℝ) : logSurvival μ t ≤ 1 :=
  sub_le_self 1 (cdf_nonneg μ _)

omit [IsProbabilityMeasure μ] in
theorem logRate_nonneg (hφ : IsRegDensity μ φ) (t : ℝ) : 0 ≤ logRate μ φ t := by
  exact mul_nonneg (Real.exp_pos t).le
    (div_nonneg (hφ.1 _) (sub_nonneg.mpr (cdf_le_one μ _)))

omit [IsProbabilityMeasure μ] in
theorem logRate_zero (hφ : IsRegDensity μ φ) (t : ℝ) (ht : logSurvival μ t = 1) :
    logRate μ φ t = 0 := by
  have hz : cdf μ (Real.exp t) = 0 := by dsimp [logSurvival, survival] at ht; linarith
  simp [logRate, genFailureRate, failureRate, hφ.2.2.2 _ hz]

omit [IsProbabilityMeasure μ] in
theorem logSurvival_deriv (hφ : IsRegDensity μ φ) (t : ℝ)
    (ht0 : 0 < logSurvival μ t) (ht1 : logSurvival μ t < 1) :
    HasDerivWithinAt (logSurvival μ) (-logRate μ φ t * logSurvival μ t) (Ici t) t := by
  have hc0 : 0 < cdf μ (Real.exp t) := by dsimp [logSurvival, survival] at ht1; linarith
  have hc1 : cdf μ (Real.exp t) < 1 := by dsimp [logSurvival, survival] at ht0; linarith
  have hd := (hφ.2.2.1 _ hc0 hc1).comp t (Real.hasDerivAt_exp t).hasDerivWithinAt
    (by intro x hx; exact Real.exp_le_exp.mpr hx)
  have hs := hd.const_sub 1
  change HasDerivWithinAt (logSurvival μ) (-(φ (Real.exp t) * Real.exp t)) (Ici t) t at hs
  convert hs using 1
  dsimp [logRate, genFailureRate, failureRate, logSurvival, survival]
  have hn : 1 - cdf μ (Real.exp t) ≠ 0 := ne_of_gt (sub_pos.mpr hc1)
  field_simp

 theorem igfr_iff_logRate (hnn : μ (Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    IsIGFR μ φ ↔ MonotoneOn (logRate μ φ) {t | 0 < logSurvival μ t} := by
  rw [igfr_iff_log_ifr hnn hφ]
  simp only [IsIFR, MonotoneOn, mem_ofPred_eq, cdf_log_map hnn hφ, log_rate hnn hφ,
    logRate, logSurvival, survival, sub_pos]

end IGFRProof

open scoped Topology Classical
open MeasureTheory ProbabilityTheory Set Filter LariviereIGFR.Char

namespace IGFRProof

variable {μ : Measure ℝ}

theorem tp2_log_iff :
    IsTP2On (fun x y => logSurvival μ (x-y)) univ univ ↔
      IsTP2On (fun x y => survival μ (x/y)) (Ioi 0) (Ioi 0) := by
  constructor
  · intro h a ha b hb c hc d hd hab hcd
    have h' := h (Real.log a) (mem_univ _) (Real.log b) (mem_univ _)
      (Real.log c) (mem_univ _) (Real.log d) (mem_univ _)
      (Real.log_lt_log ha hab) (Real.log_lt_log hc hcd)
    simpa only [logSurvival, Real.exp_sub, Real.exp_log ha, Real.exp_log hb,
      Real.exp_log hc, Real.exp_log hd] using h'
  · intro h a _ b _ c _ d _ hab hcd
    have h' := h (Real.exp a) (Real.exp_pos _) (Real.exp b) (Real.exp_pos _)
      (Real.exp c) (Real.exp_pos _) (Real.exp d) (Real.exp_pos _)
      (Real.exp_lt_exp.mpr hab) (Real.exp_lt_exp.mpr hcd)
    simpa only [logSurvival, Real.exp_sub] using h'

end IGFRProof

open Set Filter
open scoped Topology

namespace IGFRProof

theorem right_deriv_nonpos_compare (f f' : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hn : ∀ x ∈ Ico a b, f' x ≤ 0) : f b ≤ f a := by
  exact image_le_of_deriv_right_le_deriv_boundary (B := fun _ => f a) (B' := fun _ => 0) hc hd (le_refl (f a))
    continuousOn_const (fun x _ => hasDerivWithinAt_const x (Ici x) (f a)) hn
    ⟨hab, le_rfl⟩

theorem right_shift_deriv {f : ℝ → ℝ} {d x h : ℝ}
    (hf : HasDerivWithinAt f d (Ici (x + h)) (x + h)) :
    HasDerivWithinAt (fun t => f (t + h)) d (Ici x) x := by
  have hh := hf.comp x ((hasDerivWithinAt_id x (Ici x)).add_const h)
    (by intro t ht; change x ≤ t at ht; change x + h ≤ t + h; linarith)
  simpa using! hh

theorem right_deriv_nonneg_of_min {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivWithinAt f d (Ici 0) 0) (hzero : f 0 = 0)
    (hn : ∀ t, 0 ≤ t → 0 ≤ f t) : 0 ≤ d := by
  have ht : Tendsto (slope f 0) (𝓝[>] (0 : ℝ)) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hf.Ioi_of_Ici
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa [slope_def_field, hzero] using div_nonneg (hn t ht.le) ht.le

theorem tail_deriv_below_one (s r : ℝ → ℝ) (ha : Antitone s)
    (hn : ∀ x, 0 ≤ s x)
    (hd : ∀ x, 0 < s x → s x < 1 →
      HasDerivWithinAt s (-r x * s x) (Ici x) x)
    (x : ℝ) (hx : s x < 1) :
    HasDerivWithinAt s (-r x * s x) (Ici x) x := by
  rcases (hn x).eq_or_lt with hz | hp
  · have he : ∀ y ∈ Ici x, s y = 0 := by
      intro y hy
      exact le_antisymm ((ha hy).trans_eq hz.symm) (hn y)
    have hh := (hasDerivWithinAt_const x (Ici x) (0 : ℝ)).congr_of_mem he
      (by simp)
    simpa [hz.symm] using hh
  · exact hd x hp hx

end IGFRProof

open Set Filter
open scoped Topology

namespace IGFRProof

theorem tail_ratio_middle (s r : ℝ → ℝ) (hc : Continuous s) (ha : Antitone s)
    (hn : ∀ x, 0 ≤ s x)
    (hd : ∀ x, 0 < s x → s x < 1 →
      HasDerivWithinAt s (-r x * s x) (Ici x) x)
    (hr : MonotoneOn r {x | 0 < s x}) {a b δ : ℝ}
    (hab : a ≤ b) (hb : 0 < s b) (haone : s a < 1) (hδ : 0 < δ) :
    s (b + δ) / s b ≤ s (a + δ) / s a := by
  let q : ℝ → ℝ := fun x => s (x + δ) / s x
  let q' : ℝ → ℝ := fun x =>
    ((-r (x + δ) * s (x + δ)) * s x - s (x + δ) * (-r x * s x)) / (s x)^2
  have hp : ∀ x ∈ Icc a b, 0 < s x := fun x hx => hb.trans_le (ha hx.2)
  have hlt : ∀ x ∈ Icc a b, s x < 1 := fun x hx => (ha hx.1).trans_lt haone
  apply right_deriv_nonpos_compare q q' hab
  · exact (hc.comp (continuous_id.add_const δ)).continuousOn.div hc.continuousOn
      (fun x hx => (hp x hx).ne')
  · intro x hx
    have hn' := tail_deriv_below_one s r ha hn hd (x + δ)
      ((ha (by linarith : x ≤ x + δ)).trans_lt (hlt x ⟨hx.1, hx.2.le⟩))
    exact (right_shift_deriv hn').div
      (hd x (hp x ⟨hx.1, hx.2.le⟩) (hlt x ⟨hx.1, hx.2.le⟩))
      (hp x ⟨hx.1, hx.2.le⟩).ne'
  · intro x hx
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    rcases (hn (x + δ)).eq_or_lt with hz | hz
    · simp only [← hz, mul_zero, zero_mul, sub_zero, le_refl]
    · have hrate := hr (hp x ⟨hx.1, hx.2.le⟩) hz (by linarith : x ≤ x + δ)
      have hh := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (hn (x + δ)) (hn x)) (sub_nonpos.mpr hrate)
      nlinarith

theorem tail_ratio_antitone (s r : ℝ → ℝ) (hc : Continuous s) (ha : Antitone s)
    (hn : ∀ x, 0 ≤ s x) (ho : ∀ x, s x ≤ 1)
    (hd : ∀ x, 0 < s x → s x < 1 →
      HasDerivWithinAt s (-r x * s x) (Ici x) x)
    (hr : MonotoneOn r {x | 0 < s x}) (δ : ℝ) (hδ : 0 < δ) :
    AntitoneOn (fun x => s (x + δ) / s x) {x | 0 < s x} := by
  intro a _ b hb hab
  change s (b + δ) / s b ≤ s (a + δ) / s a
  rcases (ho a).eq_or_lt with haone | haone
  · rcases (ho b).eq_or_lt with hbone | hbone
    · rw [haone, hbone, div_one, div_one]
      exact ha (by linarith)
    · let K : Set ℝ := Icc a b ∩ s ⁻¹' {1}
      have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_singleton.preimage hc)
      have hKne : K.Nonempty := ⟨a, ⟨⟨le_rfl, hab⟩, haone⟩⟩
      obtain ⟨c, hcmem, hmax⟩ := hK.exists_isMaxOn hKne continuousOn_id
      have hsc : s c = 1 := hcmem.2
      have hcb : c < b := lt_of_le_of_ne hcmem.1.2 (by intro h; subst c; linarith)
      have hmiddle : ∀ t ∈ Ioo c b, s t < 1 := by
        intro t ht
        apply lt_of_le_of_ne (ho t)
        intro he
        have htK : t ∈ K := ⟨⟨hcmem.1.1.trans ht.1.le, ht.2.le⟩, he⟩
        exact (not_le_of_gt ht.1) (hmax htK)
      have hbound : ∀ t ∈ Ioo c b, s (b + δ) / s b ≤ s (t + δ) / s t := by
        intro t ht
        exact tail_ratio_middle s r hc ha hn hd hr ht.2.le hb (hmiddle t ht) hδ
      have hqc : ContinuousAt (fun t => s (t + δ) / s t) c :=
        ((hc.comp (continuous_id.add_const δ)).continuousAt).div hc.continuousAt
          (by rw [hsc]; norm_num)
      have hclose : c ∈ closure (Ioo c b) := by
        rw [closure_Ioo hcb.ne]
        exact ⟨le_rfl, hcb.le⟩
      have hbc : s (b + δ) / s b ≤ s (c + δ) / s c :=
        ContinuousWithinAt.closure_le hclose continuousWithinAt_const hqc.continuousWithinAt hbound
      apply hbc.trans
      rw [hsc, haone, div_one, div_one]
      exact ha (by linarith [hcmem.1.1])
  · exact tail_ratio_middle s r hc ha hn hd hr hab hb haone hδ

end IGFRProof

open Set Filter LariviereIGFR.Char
open scoped Topology

namespace IGFRProof

theorem shift_tp2_of_rate_monotone
    (s r : ℝ → ℝ) (hscont : Continuous s) (hsanti : Antitone s)
    (hsnonneg : ∀ x, 0 ≤ s x) (hsone : ∀ x, s x ≤ 1)
    (hderiv : ∀ x, 0 < s x → s x < 1 →
      HasDerivWithinAt s (-r x * s x) (Ici x) x)
    (hr : MonotoneOn r {x | 0 < s x}) :
    IsTP2On (fun x y => s (x - y)) univ univ := by
  intro x₁ _ x₂ _ y₁ _ y₂ _ hx hy
  have hδ : 0 < y₂ - y₁ := sub_pos.mpr hy
  have hca : x₁ - y₂ ≤ x₂ - y₂ := sub_le_sub_right hx.le _
  rcases (hsnonneg (x₂ - y₂)).eq_or_lt with hz | hz
  · have hz' : s (x₂ - y₁) = 0 := le_antisymm
      ((hsanti (by linarith : x₂ - y₂ ≤ x₂ - y₁)).trans_eq hz.symm)
      (hsnonneg _)
    simp [← hz, hz']
  · have ha : 0 < s (x₁ - y₂) := hz.trans_le (hsanti hca)
    have hh := tail_ratio_antitone s r hscont hsanti hsnonneg hsone hderiv hr
      (y₂ - y₁) hδ ha hz hca
    have h1 : x₁ - y₂ + (y₂ - y₁) = x₁ - y₁ := by ring
    have h2 : x₂ - y₂ + (y₂ - y₁) = x₂ - y₁ := by ring
    dsimp only at hh
    rw [h1, h2] at hh
    have hm := (div_le_div_iff₀ hz ha).1 hh
    nlinarith

theorem rate_monotone_of_shift_tp2
    (s r : ℝ → ℝ) (hsanti : Antitone s) (hsone : ∀ x, s x ≤ 1)
    (hrnonneg : ∀ x, 0 ≤ r x)
    (hrone : ∀ x, s x = 1 → r x = 0)
    (hderiv : ∀ x, 0 < s x → s x < 1 →
      HasDerivWithinAt s (-r x * s x) (Ici x) x)
    (htp : IsTP2On (fun x y => s (x - y)) univ univ) :
    MonotoneOn r {x | 0 < s x} := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with he | hab
  · subst b
    rfl
  rcases (hsone a).eq_or_lt with hone | hone
  · rw [hrone a hone]
    exact hrnonneg b
  have hblt : s b < 1 := (hsanti hab.le).trans_lt hone
  let f : ℝ → ℝ := fun h => s (a + h) * s b - s a * s (b + h)
  have hdA : HasDerivWithinAt (fun h => s (a + h)) (-r a * s a) (Ici 0) 0 := by
    have hd := right_shift_deriv (x := 0) (h := a) (by simpa using hderiv a ha hone)
    simpa only [add_comm, neg_mul] using! hd
  have hdB : HasDerivWithinAt (fun h => s (b + h)) (-r b * s b) (Ici 0) 0 := by
    have hd := right_shift_deriv (x := 0) (h := b) (by simpa using hderiv b hb hblt)
    simpa only [add_comm, neg_mul] using! hd
  have hf : HasDerivWithinAt f
      ((-r a * s a) * s b - s a * (-r b * s b)) (Ici 0) 0 :=
    (hdA.mul_const (s b)).sub (hdB.const_mul (s a))
  have hn : ∀ h, 0 ≤ h → 0 ≤ f h := by
    intro h hh
    rcases hh.eq_or_lt with rfl | hh
    · simp [f]
    have ht := htp (a + h) (mem_univ _) (b + h) (mem_univ _)
      0 (mem_univ _) h (mem_univ _) (by linarith) hh
    simpa only [sub_zero, add_sub_cancel_right] using ht
  have hdpos := right_deriv_nonneg_of_min hf (by simp [f]) hn
  have hprod : 0 < s a * s b := mul_pos ha hb
  have he : (-r a * s a) * s b - s a * (-r b * s b) =
      (r b - r a) * (s a * s b) := by ring
  rw [he] at hdpos
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hprod).1 hdpos)

theorem rate_monotone_iff_tp2_shift
  (s r : ℝ → ℝ)
  (hscont : Continuous s)
  (hsanti : Antitone s)
  (hsnonneg : ∀ x, 0 ≤ s x)
  (hsone : ∀ x, s x ≤ 1)
  (hrnonneg : ∀ x, 0 ≤ r x)
  (hrone : ∀ x, s x = 1 → r x = 0)
  (hderiv : ∀ x, 0 < s x → s x < 1 →
    HasDerivWithinAt s (-r x * s x) (Set.Ici x) x) :
  MonotoneOn r {x | 0 < s x} ↔
    LariviereIGFR.Char.IsTP2On (fun x y => s (x-y)) Set.univ Set.univ := by
  exact ⟨shift_tp2_of_rate_monotone s r hscont hsanti hsnonneg hsone hderiv,
    rate_monotone_of_shift_tp2 s r hsanti hsone hrnonneg hrone hderiv⟩

end IGFRProof

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem theorem_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    List.TFAE
      [ IsIGFR μ φ,
        IsIFR (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)),
        ∀ c : ℝ, 1 ≤ c → HazardRateLE μ φ (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c),
        IsTP2On (fun ξ θ => survival μ (ξ / θ)) (Set.Ioi 0) (Set.Ioi 0) ] := by
  have h12 := IGFRProof.igfr_iff_log_ifr hnn hφ
  have h13 := IGFRProof.igfr_iff_scale hnn hφ
  have h14 : IsIGFR μ φ ↔
      IsTP2On (fun ξ θ => survival μ (ξ / θ)) (Set.Ioi 0) (Set.Ioi 0) := by
    rw [IGFRProof.igfr_iff_logRate hnn hφ]
    exact (IGFRProof.rate_monotone_iff_tp2_shift (IGFRProof.logSurvival μ)
      (IGFRProof.logRate μ φ) (IGFRProof.logSurvival_continuous hφ)
      IGFRProof.logSurvival_antitone IGFRProof.logSurvival_nonneg
      IGFRProof.logSurvival_le_one (IGFRProof.logRate_nonneg hφ)
      (IGFRProof.logRate_zero hφ) (IGFRProof.logSurvival_deriv hφ)).trans
      IGFRProof.tp2_log_iff
  tfae_have 1 ↔ 2 := h12
  tfae_have 1 ↔ 3 := h13
  tfae_have 1 ↔ 4 := h14
  tfae_finish

end LariviereIGFR.Char

open MeasureTheory ProbabilityTheory LariviereIGFR.Char

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    List.TFAE
      [ IsIGFR μ φ,
        IsIFR (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)),
        ∀ c : ℝ, 1 ≤ c → HazardRateLE μ φ (μ.map (fun x => c * x)) (fun ξ => φ (ξ / c) / c),
        IsTP2On (fun ξ θ => survival μ (ξ / θ)) (Set.Ioi 0) (Set.Ioi 0) ] := by
  exact LariviereIGFR.Char.theorem_1 μ φ hnn hφ
