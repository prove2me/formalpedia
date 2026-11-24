-- Prove2me | solution 1 for IndependentInfoPricing.Main.Supplement.regular_half_tail
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T19:46:45.937859+00:00
-- url     : https://prove2.me/submissions/c5aaac8b-409e-4555-8aa7-7eae07a5bec4

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

lemma hlp_ae_fin (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD1 : IsProbabilityMeasure D)
    (hfm : Measurable f) (hDf : D = volume.withDensity f) :
    ∫⁻ x, f x ≠ ∞ := by
  have : D Set.univ = ∫⁻ x, f x := by
    rw [hDf, withDensity_apply _ MeasurableSet.univ]; simp
  rw [← this]; simp

lemma hlp_int (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD1 : IsProbabilityMeasure D)
    (hfm : Measurable f) (hDf : D = volume.withDensity f) :
    Integrable (fun t => (f t).toReal) := 
  integrable_toReal_of_lintegral_ne_top hfm.aemeasurable (hlp_ae_fin D f hD1 hfm hDf)

lemma hlp_meas (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD1 : IsProbabilityMeasure D)
    (hfm : Measurable f) (hDf : D = volume.withDensity f) {s : Set ℝ} (hs : MeasurableSet s) :
    (D s).toReal = ∫ x in s, (f x).toReal := by
  have hfin := ae_lt_top hfm (hlp_ae_fin D f hD1 hfm hDf)
  rw [integral_toReal hfm.aemeasurable (ae_restrict_of_ae hfin), hDf, withDensity_apply _ hs]

lemma hlp_noatoms (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hDf : D = volume.withDensity f) :
    NullSingletonClass D := ⟨fun x => by
  have := withDensity_absolutelyContinuous (volume : Measure ℝ) f (s := {x}) (by simp)
  rw [← hDf] at this; exact this⟩

lemma hlp_surv (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD1 : IsProbabilityMeasure D)
    (hfm : Measurable f) (hDf : D = volume.withDensity f) (t : ℝ) :
    survival D t = 1 - ((∫ x in Set.Iic 0, (f x).toReal) + ∫ x in (0:ℝ)..t, (f x).toReal) := by
  have := hlp_noatoms D f hDf
  have hint := hlp_int D f hD1 hfm hDf
  have h1 : survival D t = 1 - ∫ x in Set.Iic t, (f x).toReal := by
    unfold survival
    have : D (Set.Ici t) = D (Set.Ioi t) := measure_congr Ioi_ae_eq_Ici.symm
    rw [this, ← hlp_meas D f hD1 hfm hDf measurableSet_Iic, ← Set.compl_Iic,
      prob_compl_eq_one_sub measurableSet_Iic, ENNReal.toReal_sub_of_le prob_le_one (by simp)]
    simp
  rw [h1, ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
  ring

lemma hlp_cont (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD1 : IsProbabilityMeasure D)
    (hfm : Measurable f) (hDf : D = volume.withDensity f) :
    Continuous (survival D) := by
  have hint := hlp_int D f hD1 hfm hDf
  have : survival D = fun t => 1 - ((∫ x in Set.Iic 0, (f x).toReal) + ∫ x in (0:ℝ)..t, (f x).toReal) :=
    funext (hlp_surv D f hD1 hfm hDf)
  rw [this]
  exact continuous_const.sub (continuous_const.add
    (intervalIntegral.continuous_primitive (fun a b => hint.intervalIntegrable) 0))

lemma hlp_deriv (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD1 : IsProbabilityMeasure D)
    (hfm : Measurable f) (hDf : D = volume.withDensity f) (t : ℝ)
    (hc : ContinuousAt (fun x => (f x).toReal) t) :
    HasDerivAt (survival D) (-(f t).toReal) t := by
  have hint := hlp_int D f hD1 hfm hDf
  have : survival D = fun t => 1 - ((∫ x in Set.Iic 0, (f x).toReal) + ∫ x in (0:ℝ)..t, (f x).toReal) :=
    funext (hlp_surv D f hD1 hfm hDf)
  rw [this]
  have h := intervalIntegral.integral_hasDerivAt_right (hint.intervalIntegrable (a := 0) (b := t))
    (hfm.ennreal_toReal.stronglyMeasurable.stronglyMeasurableAtFilter) hc
  simpa using (h.const_add _).const_sub 1


lemma hlp_surv_one (D : Measure ℝ) [IsProbabilityMeasure D] (t : ℝ) (h : D (Set.Iio t) = 0) :
    survival D t = 1 := by
  unfold survival
  rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, h]; simp

lemma hlp_surv_anti (D : Measure ℝ) [IsProbabilityMeasure D] {s t : ℝ} (h : s ≤ t) :
    survival D t ≤ survival D s := by
  unfold survival
  exact ENNReal.toReal_mono (by simp) (measure_mono (Set.Ici_subset_Ici.2 h))

lemma hlp_supp (D : Measure ℝ) : lawSupport D = D.support := by
  ext x
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro h U hU
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
    have := h r hr
    refine lt_of_lt_of_le this (measure_mono ?_)
    intro y hy
    apply hrU
    rw [Real.ball_eq_Ioo]; exact hy
  · intro h r hr
    exact h _ (Ioo_mem_nhds (by linarith) (by linarith))

lemma hlp_Jnull (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD1 : IsProbabilityMeasure D)
    (hDf : D = volume.withDensity f) (hOC : (lawSupport D).OrdConnected) :
    D (interior (lawSupport D))ᶜ = 0 := by
  have hconv : Convex ℝ (lawSupport D) := convex_iff_ordConnected.2 hOC
  have hfr : D (frontier (lawSupport D)) = 0 := by
    have := withDensity_absolutelyContinuous (volume : Measure ℝ) f
      (s := frontier (lawSupport D)) (hconv.addHaar_frontier (μ := volume))
    rwa [← hDf] at this
  have hsc : D (lawSupport D)ᶜ = 0 := by rw [hlp_supp]; exact Measure.measure_compl_support
  refine measure_mono_null ?_ (measure_union_null hsc hfr)
  intro x hx
  by_cases h : x ∈ lawSupport D
  · right; exact ⟨subset_closure h, hx⟩
  · left; exact h

lemma quasi_nonneg (k k' : ℝ → ℝ) (a p : ℝ) (hap : a < p)
    (hcont : ContinuousOn k (Set.Icc a p))
    (hd : ∀ t ∈ Set.Ioo a p, HasDerivAt k (k' t) t)
    (hpat : ∀ s ∈ Set.Ioo a p, ∀ s' ∈ Set.Ioo a p, s < s' → k' s < 0 → k' s' < 0)
    (ha : 0 ≤ k a) (hp : 0 ≤ k p) : ∀ t ∈ Set.Icc a p, 0 ≤ k t := by
  intro t ht
  by_contra hneg
  push_neg at hneg
  have hat : a < t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
  have htp : t < p := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
  obtain ⟨c, hc, hck⟩ := exists_hasDerivAt_eq_slope k k' hat
    (hcont.mono (Set.Icc_subset_Icc le_rfl htp.le)) (fun x hx => hd x ⟨hx.1, by linarith [hx.2]⟩)
  have hneg' : k' c < 0 := by
    rw [hck]; apply div_neg_of_neg_of_pos <;> linarith
  have hcm : c ∈ Set.Ioo a p := ⟨hc.1, by linarith [hc.2]⟩
  have hanti : AntitoneOn k (Set.Icc c p) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc c p)
    · exact hcont.mono (Set.Icc_subset_Icc hc.1.le le_rfl)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x ⟨by linarith [hx.1, hc.1], hx.2⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxm : x ∈ Set.Ioo a p := ⟨by linarith [hx.1, hc.1], hx.2⟩
      rw [(hd x hxm).deriv]
      exact (hpat c hcm x hxm hx.1 hneg').le
  have := hanti ⟨hc.2.le, htp.le⟩ ⟨by linarith [hc.2], le_rfl⟩ htp.le
  linarith


lemma core_half (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hneg : D (Set.Iio 0) = 0)
    (hI : IntervalDensity D f) (hR : Regular D f) (p0 : ℝ) (hp0 : 0 < p0)
    (hq : 0 < survival D p0) (hq2 : survival D p0 < 1 / 2) :
    1 / 2 ≤ survival D (p0 * survival D p0) := by
  obtain ⟨hD1, hfm, hDf, hOC, hpos, hC1⟩ := hI
  have hconv : Convex ℝ (lawSupport D) := convex_iff_ordConnected.2 hOC
  have hJo : IsOpen (interior (lawSupport D)) := isOpen_interior
  have hJc : (interior (lawSupport D)).OrdConnected :=
    convex_iff_ordConnected.1 hconv.interior
  have hnull := hlp_Jnull D f hD1 hDf hOC
  set J := interior (lawSupport D) with hJdef
  have hJne : J.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    rw [hn, Set.compl_empty] at hnull
    simp at hnull
  have hJnn : ∀ j ∈ J, 0 ≤ j := by
    intro j hj
    by_contra hlt
    push_neg at hlt
    have h := (interior_subset hj) (-j) (by linarith)
    have : D (Set.Ioo (j - -j) (j + -j)) = 0 :=
      measure_mono_null (fun y hy => by simp only [Set.mem_Iio]; linarith [hy.2]) hneg
    rw [this] at h; exact lt_irrefl _ h
  have hbdd : BddBelow J := ⟨0, hJnn⟩
  set a := sInf J with ha_def
  have hSa : ∀ t ≤ a, survival D t = 1 := by
    intro t ht
    have := hD1
    apply hlp_surv_one
    refine measure_mono_null (fun y hy => ?_) hnull
    intro hyJ
    have := csInf_le hbdd hyJ
    simp only [Set.mem_Iio] at hy
    linarith
  have hS0 := hlp_surv_anti D (le_refl p0)
  have hap : a < p0 := by
    by_contra h
    push_neg at h
    have := hSa p0 h
    linarith
  have hp0J : p0 ∈ J := by
    by_contra hn
    obtain ⟨j, hj, hjp⟩ := exists_lt_of_csInf_lt hJne hap
    have hsub : Set.Ici p0 ⊆ Jᶜ := by
      intro y hy hyJ
      exact hn (hJc.out hj hyJ ⟨hjp.le, hy⟩)
    have h0 : survival D p0 = 0 := by
      unfold survival
      rw [measure_mono_null hsub hnull]; simp
    linarith
  have hJs : ∀ s, a < s → s ≤ p0 → s ∈ J := by
    intro s hs hsp
    obtain ⟨j, hj, hjs⟩ := exists_lt_of_csInf_lt hJne hs
    exact hJc.out hj hp0J ⟨hjs.le, hsp⟩
  haveI := hD1
  have hSc := hlp_cont D f hD1 hfm hDf
  set q0 := survival D p0 with hq0
  set c := p0 * q0 / (1 - q0) with hc
  have h1q : 0 < 1 - q0 := by linarith
  let k : ℝ → ℝ := fun t => t * survival D t - c * (1 - survival D t)
  let k' : ℝ → ℝ := fun t => survival D t - (t + c) * (f t).toReal
  have hgpos : ∀ t ∈ J, 0 < (f t).toReal := fun t ht =>
    ENNReal.toReal_pos (ne_of_gt (hpos t ht).2) (hpos t ht).1
  have hd : ∀ t ∈ Set.Ioo a p0, HasDerivAt k (k' t) t := by
    intro t ht
    have htJ := hJs t ht.1 ht.2.le
    have hgc : ContinuousAt (fun x => (f x).toReal) t :=
      (hC1.continuousOn).continuousAt (hJo.mem_nhds htJ)
    have hS := hlp_deriv D f hD1 hfm hDf t hgc
    have := ((hasDerivAt_id t).mul hS).sub (((hasDerivAt_const t (1:ℝ)).sub hS).const_mul c)
    refine this.congr_deriv ?_
    simp only [k', id]; ring
  have hcont : ContinuousOn k (Set.Icc a p0) :=
    ((continuous_id.mul hSc).sub (continuous_const.mul (continuous_const.sub hSc))).continuousOn
  have hpat : ∀ s ∈ Set.Ioo a p0, ∀ s' ∈ Set.Ioo a p0, s < s' → k' s < 0 → k' s' < 0 := by
    intro s hs s' hs' hss hk
    have hsJ := hJs s hs.1 hs.2.le
    have hsJ' := hJs s' hs'.1 hs'.2.le
    have hm := hR hsJ hsJ' hss.le
    have g1 := hgpos s hsJ
    have g2 := hgpos s' hsJ'
    simp only [virtualValue] at hm
    simp only [k'] at hk ⊢
    have e1 : survival D s / (f s).toReal < s + c := by
      rw [div_lt_iff₀ g1]; linarith
    have e2 : survival D s' / (f s').toReal < s' + c := by linarith
    rw [div_lt_iff₀ g2] at e2
    linarith
  have hka : 0 ≤ k a := by
    simp only [k]; rw [hSa a le_rfl]; linarith [ha_def ▸ (le_csInf hJne hJnn : 0 ≤ sInf J)]
  have hkp : 0 ≤ k p0 := by
    simp only [k]; rw [← hq0]
    have : c * (1 - q0) = p0 * q0 := by rw [hc]; field_simp
    nlinarith
  have hmain := quasi_nonneg k k' a p0 hap hcont hd hpat hka hkp
  have hr0 : 0 < p0 * q0 := mul_pos hp0 hq
  have hrp : p0 * q0 < p0 := by nlinarith
  by_cases hra : p0 * q0 ≤ a
  · rw [hSa _ hra]; norm_num
  · push_neg at hra
    have hk := hmain (p0 * q0) ⟨hra.le, hrp.le⟩
    simp only [k] at hk
    set q1 := survival D (p0 * q0) with hq1
    have hq1nn : 0 ≤ q1 := ENNReal.toReal_nonneg
    have : (p0 * q0 * q1 - c * (1 - q1)) * (1 - q0) = p0 * q0 * (q1 * (1 - q0) - (1 - q1)) := by
      rw [hc]; field_simp
    have hpos' : 0 ≤ p0 * q0 * (q1 * (1 - q0) - (1 - q1)) := by
      rw [← this]; exact mul_nonneg hk h1q.le
    have := nonneg_of_mul_nonneg_right hpos' hr0
    nlinarith


theorem regular_half_tail (D : Measure ℝ) (hD : RegularMagnitude D) : HalfTail D := by
  obtain ⟨f, ⟨hneg, hI, p0, hp0, hrev⟩, hR⟩ := hD
  have hD1 : IsProbabilityMeasure D := hI.1
  set q0 := survival D p0 with hq0
  have hDI : D (Set.Ici p0) = ENNReal.ofReal q0 := by
    rw [hq0]; unfold survival; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hq0nn : 0 ≤ q0 := ENNReal.toReal_nonneg
  have hsr : scalarRevenue D = ENNReal.ofReal (p0 * q0) := by
    rw [hrev, hDI, ENNReal.ofReal_mul hp0]
  have hS0 : survival D 0 = 1 := by
    have := hD1; exact hlp_surv_one D 0 hneg
  have hkey : 1 / 2 ≤ survival D (p0 * q0) := by
    by_cases h1 : 1 / 2 ≤ q0
    · calc (1:ℝ) / 2 ≤ q0 := h1
        _ ≤ survival D (p0 * q0) := by
          have := hD1
          apply hlp_surv_anti
          have : q0 ≤ 1 := by
            rw [hq0]; unfold survival
            exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using prob_le_one)
          nlinarith
    · push_neg at h1
      rcases hp0.eq_or_lt with h0 | h0
      · rw [← h0, zero_mul, hS0]; norm_num
      rcases hq0nn.eq_or_lt with h2 | h2
      · rw [← h2, mul_zero, hS0]; norm_num
      exact core_half D f hneg hI hR p0 h0 h2 h1
  have hsub : Set.Ici (p0 * q0) ⊆ {x | scalarRevenue D ≤ ENNReal.ofReal x} := by
    intro x hx
    rw [hsr]; exact ENNReal.ofReal_le_ofReal hx
  refine le_trans ?_ (measure_mono hsub)
  have : D (Set.Ici (p0 * q0)) = ENNReal.ofReal (survival D (p0 * q0)) := by
    unfold survival; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [this]
  calc (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hkey

end IndependentInfoPricing.Main.Supplement

theorem solution (D : MeasureTheory.Measure ℝ)
    (hD : IndependentInfoPricing.Main.Supplement.RegularMagnitude D) :
    IndependentInfoPricing.Main.HalfTail D :=
  IndependentInfoPricing.Main.Supplement.regular_half_tail D hD
