-- Prove2me | solution 1 for MinBuying.triangular_continuous_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:46:56.744008+00:00
-- url     : https://prove2.me/submissions/f0efbf9c-44b6-4b8e-b80c-a409e1c848d8

import Theorems.Thm_MinBuying_triangular_law_specification

open MeasureTheory Set Filter MinBuying
open scoped Topology
noncomputable section

private def cut (a v : ℝ) : ℝ := v / (v + a)

private def smoothValue (a v δ u : ℝ) : ℝ :=
  min v (a * u / (1-u)) + δ * max 0 (u - cut a v) / (1 - cut a v)

private def smoothLaw (a v δ : ℝ) : Measure ℝ :=
  Measure.map (smoothValue a v δ) unitIntervalLaw

private lemma cut_bounds (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    0 < cut a v ∧ cut a v < 1 := by
  have hd : 0 < v+a := add_pos hv ha
  exact ⟨div_pos hv hd, (div_lt_one hd).mpr (by linarith)⟩

private lemma cut_identity (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    (v+a) * cut a v = v := by
  unfold cut
  field_simp

private lemma ratio_le_iff (a v u : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hu : u < 1) : a*u/(1-u) ≤ v ↔ u ≤ cut a v := by
  rw [div_le_iff₀ (sub_pos.mpr hu)]
  unfold cut
  rw [le_div_iff₀ (add_pos hv ha)]
  constructor <;> intro h <;> nlinarith

private lemma ratio_lt_iff (a v u : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hu : u < 1) : a*u/(1-u) < v ↔ u < cut a v := by
  rw [div_lt_iff₀ (sub_pos.mpr hu)]
  unfold cut
  rw [lt_div_iff₀ (add_pos hv ha)]
  constructor <;> intro h <;> nlinarith

private lemma smooth_left (a v δ u : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hu : u < 1) (hur : u ≤ cut a v) :
    smoothValue a v δ u = a*u/(1-u) := by
  simp only [smoothValue, min_eq_right ((ratio_le_iff a v u ha hv hu).mpr hur),
    max_eq_left (sub_nonpos.mpr hur), mul_zero, zero_div, add_zero]

private lemma smooth_right (a v δ u : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hu : u < 1) (hru : cut a v ≤ u) :
    smoothValue a v δ u = v + δ*(u-cut a v)/(1-cut a v) := by
  have hrat : v ≤ a*u/(1-u) := by
    by_contra h
    exact (not_lt_of_ge hru) ((ratio_lt_iff a v u ha hv hu).mp (lt_of_not_ge h))
  simp only [smoothValue, min_eq_left hrat, max_eq_right (sub_nonneg.mpr hru)]

private lemma smooth_measurable (a v δ : ℝ) : Measurable (smoothValue a v δ) := by
  unfold smoothValue
  fun_prop

private lemma smooth_continuous (a v δ : ℝ) :
    ContinuousOn (smoothValue a v δ) (Ioo (0 : ℝ) 1) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold smoothValue
  fun_prop (disch := linarith [hx.2])

private lemma smooth_strictMono (a v δ : ℝ) (ha : 0 < a) (hv : 0 < v) (hδ : 0 < δ) :
    StrictMonoOn (smoothValue a v δ) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hd : 0 < 1-cut a v := sub_pos.mpr (cut_bounds a v ha hv).2
  by_cases hxr : x ≤ cut a v
  · rw [smooth_left a v δ x ha hv hx.2 hxr]
    by_cases hyr : y ≤ cut a v
    · rw [smooth_left a v δ y ha hv hy.2 hyr]
      apply (div_lt_div_iff₀ (sub_pos.mpr hx.2) (sub_pos.mpr hy.2)).mpr
      nlinarith [mul_pos ha (sub_pos.mpr hxy)]
    · rw [smooth_right a v δ y ha hv hy.2 (le_of_not_ge hyr)]
      have hr : a*x/(1-x) ≤ v := (ratio_le_iff a v x ha hv hx.2).mpr hxr
      have hp : 0 < δ*(y-cut a v)/(1-cut a v) :=
        div_pos (mul_pos hδ (sub_pos.mpr (lt_of_not_ge hyr))) hd
      linarith
  · have hry : cut a v ≤ y := (le_of_not_ge hxr).trans hxy.le
    rw [smooth_right a v δ x ha hv hx.2 (le_of_not_ge hxr),
      smooth_right a v δ y ha hv hy.2 hry]
    have hh : δ*(x-cut a v)/(1-cut a v) < δ*(y-cut a v)/(1-cut a v) :=
      (div_lt_div_iff_of_pos_right hd).mpr (mul_lt_mul_of_pos_left (by linarith) hδ)
    linarith

private lemma smooth_range (a v δ u : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hδ : 0 < δ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 ≤ smoothValue a v δ u ∧ smoothValue a v δ u ≤ v+δ := by
  have hd : 0 < 1-cut a v := sub_pos.mpr (cut_bounds a v ha hv).2
  have hbase : 0 ≤ min v (a*u/(1-u)) :=
    le_min hv.le (div_nonneg (mul_nonneg ha.le hu.1.le) (sub_nonneg.mpr hu.2.le))
  have hadd : 0 ≤ δ * max 0 (u-cut a v)/(1-cut a v) :=
    div_nonneg (mul_nonneg hδ.le (le_max_left _ _)) hd.le
  have haddU : δ * max 0 (u-cut a v)/(1-cut a v) ≤ δ := by
    apply (div_le_iff₀ hd).mpr
    apply mul_le_mul_of_nonneg_left ?_ hδ.le
    exact max_le hd.le (by linarith [hu.2])
  unfold smoothValue
  exact ⟨add_nonneg hbase hadd, add_le_add (min_le_left _ _) haddU⟩

private lemma smooth_probability (a v δ : ℝ) : IsProbabilityMeasure (smoothLaw a v δ) := by
  letI : IsProbabilityMeasure unitIntervalLaw := ⟨by simp [unitIntervalLaw, Real.volume_Ioo]⟩
  exact Measure.isProbabilityMeasure_map (smooth_measurable a v δ).aemeasurable

private lemma smooth_support (a v δ : ℝ) (ha : 0 < a) (hv : 0 < v) (hδ : 0 < δ) :
    ∀ᵐ x ∂smoothLaw a v δ, x ∈ Icc (0 : ℝ) (v+δ) := by
  unfold smoothLaw
  apply (ae_map_iff (smooth_measurable a v δ).aemeasurable measurableSet_Icc).mpr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with u hu
  exact smooth_range a v δ u ha hv hδ hu

private lemma smooth_ac (a v δ : ℝ) (ha : 0 < a) (hv : 0 < v) (hδ : 0 < δ) :
    smoothLaw a v δ ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hsz
  let L : ℝ → ℝ := fun x => x/(x+a)
  let R : ℝ → ℝ := fun x => cut a v + (1-cut a v)*(x-v)/δ
  have hLdiff : DifferentiableOn ℝ L (s ∩ Ici (0 : ℝ)) := by
    intro x hx
    have hxa : x+a ≠ 0 := (add_pos_of_nonneg_of_pos hx.2 ha).ne'
    apply DifferentiableAt.differentiableWithinAt
    dsimp [L]
    fun_prop
  have hRdiff : DifferentiableOn ℝ R s := by
    unfold R
    fun_prop
  have hLnull : volume (L '' (s ∩ Ici (0 : ℝ))) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hLdiff
      (measure_mono_null inter_subset_left hsz)
  have hRnull : volume (R '' s) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hRdiff hsz
  unfold smoothLaw unitIntervalLaw
  rw [Measure.map_apply (smooth_measurable a v δ) hs,
    Measure.restrict_apply ((smooth_measurable a v δ) hs)]
  apply measure_mono_null (t := (L '' (s ∩ Ici (0 : ℝ))) ∪ (R '' s)) ?_
    (measure_union_null hLnull hRnull)
  rintro u ⟨hu, hu0, hu1⟩
  by_cases hur : u ≤ cut a v
  · apply Or.inl
    refine ⟨smoothValue a v δ u, ⟨hu, (smooth_range a v δ u ha hv hδ ⟨hu0,hu1⟩).1⟩, ?_⟩
    rw [smooth_left a v δ u ha hv hu1 hur]
    have hd : 1-u ≠ 0 := (sub_pos.mpr hu1).ne'
    have he : a*u/(1-u)+a = a/(1-u) := by field_simp; ring
    dsimp [L]
    rw [he]
    field_simp
  · apply Or.inr
    refine ⟨smoothValue a v δ u, hu, ?_⟩
    rw [smooth_right a v δ u ha hv hu1 (le_of_not_ge hur)]
    dsimp [R]
    have hd : 1-cut a v ≠ 0 := (sub_pos.mpr (cut_bounds a v ha hv).2).ne'
    field_simp
    ring

private lemma smooth_cdf_at (a v δ u : ℝ) (ha : 0 < a) (hv : 0 < v) (hδ : 0 < δ)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    cdf (smoothLaw a v δ) (smoothValue a v δ u) = u := by
  have hm := smooth_strictMono a v δ ha hv hδ
  have he : (smoothValue a v δ) ⁻¹' Iic (smoothValue a v δ u) ∩ Ioo 0 1 = Ioc 0 u := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨ht,ht0,ht1⟩
      refine ⟨ht0, ?_⟩
      by_contra h
      exact (not_lt_of_ge ht) (hm hu ⟨ht0,ht1⟩ (lt_of_not_ge h))
    · rintro ⟨ht0,htu⟩
      have ht1 := htu.trans_lt hu.2
      exact ⟨hm.monotoneOn ⟨ht0,ht1⟩ hu htu, ht0, ht1⟩
  unfold cdf smoothLaw unitIntervalLaw
  rw [Measure.map_apply (smooth_measurable a v δ) measurableSet_Iic,
    Measure.restrict_apply ((smooth_measurable a v δ) measurableSet_Iic), he, Real.volume_Ioc]
  simpa using ENNReal.toReal_ofReal hu.1.le

private lemma smooth_quantile_at (a v δ u : ℝ) (ha : 0 < a) (hv : 0 < v) (hδ : 0 < δ)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantile (smoothLaw a v δ) u = smoothValue a v δ u := by
  letI := smooth_probability a v δ
  have hw : smoothValue a v δ u ∈ {x : ℝ | 0 ≤ x ∧ u ≤ cdf (smoothLaw a v δ) x} :=
    ⟨(smooth_range a v δ u ha hv hδ hu).1, (smooth_cdf_at a v δ u ha hv hδ hu).ge⟩
  unfold quantile
  apply le_antisymm (csInf_le ⟨0, fun _ h => h.1⟩ hw)
  apply le_csInf ⟨_, hw⟩
  rintro p ⟨hp0,hp⟩
  by_contra h
  have hpu : p < smoothValue a v δ u := lt_of_not_ge h
  have hc : ContinuousAt (smoothValue a v δ) u :=
    (smooth_continuous a v δ u hu).continuousAt (isOpen_Ioo.mem_nhds hu)
  have he : ∀ᶠ t : ℝ in 𝓝[<] u, p < smoothValue a v δ t ∧ 0 < t ∧ t < u := by
    filter_upwards [(hc.tendsto.eventually (eventually_gt_nhds hpu)).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds hu.1).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hpt ht0 htu
    exact ⟨hpt,ht0,htu⟩
  obtain ⟨t,hpt,ht0,htu⟩ := he.exists
  have ht1 : t < 1 := htu.trans hu.2
  have hmon : cdf (smoothLaw a v δ) p ≤ cdf (smoothLaw a v δ) (smoothValue a v δ t) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hpt.le))
  rw [smooth_cdf_at a v δ t ha hv hδ ⟨ht0,ht1⟩] at hmon
  linarith

private lemma smooth_regular (a v δ : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hδ : 0 < δ) (hδa : δ < a) : Regular (smoothLaw a v δ) := by
  let q₀ := 1-cut a v
  have hq₀ : 0 < q₀ := sub_pos.mpr (cut_bounds a v ha hv).2
  have hqa : (v+a)*q₀ = a := by
    dsimp [q₀]
    nlinarith [cut_identity a v ha hv]
  have hvq : v = a/q₀-a := by
    have hh : v+a = a/q₀ := (eq_div_iff hq₀.ne').mpr hqa
    linarith
  let top : ℝ → ℝ := fun q => (v+δ)*q - (δ/q₀)*q^2
  let tail : ℝ → ℝ := fun q => a*(1-q)
  have hgap (q : ℝ) : top q-tail q = (q-q₀)*(a-δ*q)/q₀ := by
    dsimp [top,tail]
    rw [hvq]
    field_simp
    ring
  have hcurve : ∀ q ∈ Ioo (0 : ℝ) 1,
      revenueQuantile (smoothLaw a v δ) q = min (top q) (tail q) := by
    intro q hq
    have hu : 1-q ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hq.2], by linarith [hq.1]⟩
    rw [revenueQuantile, smooth_quantile_at a v δ (1-q) ha hv hδ hu]
    have hfac : 0 ≤ a-δ*q := by nlinarith [hq.2]
    by_cases hqq : q ≤ q₀
    · have hru : cut a v ≤ 1-q := by dsimp [q₀] at hqq; linarith
      rw [smooth_right a v δ (1-q) ha hv hu.2 hru]
      have hle : top q ≤ tail q := by
        have := div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hqq) hfac) hq₀.le
        rw [← hgap q] at this
        linarith
      rw [min_eq_left hle]
      dsimp [top,q₀]
      have hd : 1-cut a v ≠ 0 := hq₀.ne'
      field_simp
      ring
    · have hur : 1-q ≤ cut a v := by dsimp [q₀] at hqq; linarith
      rw [smooth_left a v δ (1-q) ha hv hu.2 hur]
      have hle : tail q ≤ top q := by
        have := div_nonneg (mul_nonneg (sub_nonneg.mpr (le_of_not_ge hqq)) hfac) hq₀.le
        rw [← hgap q] at this
        linarith
      rw [min_eq_right hle]
      dsimp [tail]
      rw [show 1-(1-q) = q by ring]
      have hqn : q ≠ 0 := hq.1.ne'
      field_simp
  have ht : ConcaveOn ℝ (Ioo (0 : ℝ) 1) top := by
    have hlin : ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun q => (v+δ)*q) := by
      simpa only [id_eq, smul_eq_mul] using
        ConcaveOn.smul (add_nonneg hv.le hδ.le) (concaveOn_id (convex_Ioo (0 : ℝ) 1))
    have hsq : ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun q => (δ/q₀)*q^2) := by
      simpa only [smul_eq_mul] using ConvexOn.smul (div_nonneg hδ.le hq₀.le)
        ((convexOn_pow 2).subset (fun _ h => h.1.le) (convex_Ioo (0 : ℝ) 1))
    exact hlin.sub hsq
  have hb : ConcaveOn ℝ (Ioo (0 : ℝ) 1) tail := by
    refine ⟨convex_Ioo 0 1, ?_⟩
    intro x _ y _ r s hr hs hrs
    simp only [tail,smul_eq_mul]
    nlinarith [congrArg (fun t => a*t) hrs]
  exact (ht.inf hb).congr (fun q hq => (hcurve q hq).symm)

private lemma smooth_cap (a v δ : ℝ) (ha : 0 < a) (hv : 0 < v) (hδ : 0 < δ) :
    rejection (smoothLaw a v δ) v = rejection (triangularLaw a v) v := by
  haveI : NullSingletonClass (smoothLaw a v δ) := ⟨fun x => smooth_ac a v δ ha hv hδ (by simp)⟩
  have hr := cut_bounds a v ha hv
  have he : smoothValue a v δ (cut a v) = v := by
    rw [smooth_left a v δ (cut a v) ha hv hr.2 le_rfl]
    apply (div_eq_iff (sub_pos.mpr hr.2).ne').mpr
    nlinarith [cut_identity a v ha hv]
  have hc := smooth_cdf_at a v δ (cut a v) ha hv hδ hr
  rw [he] at hc
  have hrej : rejection (smoothLaw a v δ) v = cdf (smoothLaw a v δ) v := by
    unfold rejection cdf
    rw [measure_congr Iio_ae_eq_Iic]
  rw [hrej,hc,(triangular_law_specification a v ha hv).2.2.1]
  simp [triangularReject, not_le_of_gt hv, cut]

private lemma smooth_shift (a v δ : ℝ) (ha : 0 < a) (hv : 0 < v) (hδ : 0 < δ)
    (p : ℝ) : rejection (triangularLaw a v) (p-δ) ≤ rejection (smoothLaw a v δ) p := by
  letI := smooth_probability a v δ
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  unfold triangularLaw smoothLaw unitIntervalLaw
  have hm : Measurable (fun u : ℝ => min v (a*u/(1-u))) := by fun_prop
  rw [Measure.map_apply hm measurableSet_Iio,
    Measure.map_apply (smooth_measurable a v δ) measurableSet_Iio,
    Measure.restrict_apply (hm measurableSet_Iio),
    Measure.restrict_apply ((smooth_measurable a v δ) measurableSet_Iio)]
  apply measure_mono
  rintro u ⟨hup,hu0,hu1⟩
  refine ⟨?_,hu0,hu1⟩
  change smoothValue a v δ u < p
  have hd : 0 < 1-cut a v := sub_pos.mpr (cut_bounds a v ha hv).2
  have hterm : δ*max 0 (u-cut a v)/(1-cut a v) ≤ δ := by
    apply (div_le_iff₀ hd).mpr
    apply mul_le_mul_of_nonneg_left ?_ hδ.le
    exact max_le hd.le (by linarith)
  change min v (a*u/(1-u)) < p-δ at hup
  unfold smoothValue
  linarith

theorem solution (a v δ : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hδ : 0 < δ) (hδa : δ < a) :
    ∃ F : Measure ℝ,
      ContinuousRegular F ∧
      (∀ᵐ x ∂F, x ∈ Icc (0 : ℝ) (v+δ)) ∧
      rejection F v = rejection (triangularLaw a v) v ∧
      (∀ p : ℝ, rejection (triangularLaw a v) (p-δ) ≤ rejection F p) := by
  have hs := smooth_support a v δ ha hv hδ
  exact ⟨smoothLaw a v δ,
    ⟨⟨smooth_probability a v δ, hs.mono (fun _ h => h.1)⟩,
      smooth_ac a v δ ha hv hδ, smooth_regular a v δ ha hv hδ hδa⟩,
    hs, smooth_cap a v δ ha hv hδ, smooth_shift a v δ ha hv hδ⟩

