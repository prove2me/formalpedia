-- Prove2me | solution 1 for MinBuying.regular_triangular_minorant
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:29:40.732988+00:00
-- url     : https://prove2.me/submissions/89e2cd3c-6c34-4138-a9a9-79abc104a4bc

import Theorems.Thm_MinBuying_triangular_law_specification

open MeasureTheory Set Filter MinBuying
open scoped Topology
noncomputable section

private lemma cdf_prob (F : Measure ℝ) [IsProbabilityMeasure F] :
    cdf F = fun x => ProbabilityTheory.cdf F x := by
  funext x
  exact (ProbabilityTheory.cdf_eq_real F x).symm

private lemma cdf_nonneg (F : Measure ℝ) (x : ℝ) : 0 ≤ cdf F x := ENNReal.toReal_nonneg

private lemma reject_le_cdf (F : Measure ℝ) [IsProbabilityMeasure F] (x : ℝ) :
    rejection F x ≤ cdf F x :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Iio_subset_Iic_self)

private lemma reject_bounds (F : Measure ℝ) [IsProbabilityMeasure F] (x : ℝ) :
    0 ≤ rejection F x ∧ rejection F x ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  exact (reject_le_cdf F x).trans (by rw [cdf_prob F]; exact ProbabilityTheory.cdf_le_one F x)

private lemma quantile_set_nonempty (F : Measure ℝ) [IsProbabilityMeasure F]
    (u : ℝ) (hu : u < 1) : {x : ℝ | 0 ≤ x ∧ u ≤ cdf F x}.Nonempty := by
  have hlim : Tendsto (cdf F) atTop (𝓝 1) := by
    rw [cdf_prob F]
    exact ProbabilityTheory.tendsto_cdf_atTop F
  have he : ∀ᶠ x : ℝ in atTop, 0 ≤ x ∧ u < cdf F x :=
    (eventually_ge_atTop 0).and (hlim.eventually (eventually_gt_nhds hu))
  obtain ⟨x, hx0, hxu⟩ := he.exists
  exact ⟨x, hx0, hxu.le⟩

private lemma quantile_nonneg (F : Measure ℝ) [IsProbabilityMeasure F]
    (u : ℝ) (hu : u < 1) : 0 ≤ quantile F u :=
  le_csInf (quantile_set_nonempty F u hu) (fun _ hx => hx.1)

private lemma quantile_below (F : Measure ℝ) (u p : ℝ) (hp : 0 ≤ p)
    (hu : u ≤ cdf F p) : quantile F u ≤ p :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hp, hu⟩

private lemma quantile_above (F : Measure ℝ) [IsProbabilityMeasure F]
    (u p : ℝ) (hu1 : u < 1) (hu : rejection F p < u) : p ≤ quantile F u := by
  apply le_csInf (quantile_set_nonempty F u hu1)
  rintro x ⟨_, hx⟩
  by_contra hpx
  have hxp : x < p := lt_of_not_ge hpx
  have hc : cdf F x ≤ rejection F p :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iio.mpr hxp))
  linarith

private lemma concave_chord_to_one (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Ioo (0 : ℝ) 1) f)
    (hfn : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x)
    (r x : ℝ) (hr : 0 < r) (hrx : r < x) (hx : x < 1) :
    f r * (1 - x) / (1 - r) ≤ f x := by
  have hr1 : r < 1 := hrx.trans hx
  have hstep : ∀ y, x < y → y < 1 → f r * (y - x) / (y - r) ≤ f x := by
    intro y hxy hy
    have hry : 0 < y - r := sub_pos.mpr (hrx.trans hxy)
    let s := (y - x) / (y - r)
    let t := (x - r) / (y - r)
    have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr hxy.le) hry.le
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hrx.le) hry.le
    have hst : s + t = 1 := by dsimp [s,t]; field_simp; ring
    have hpt : s * r + t * y = x := by dsimp [s,t]; field_simp; ring
    have hc := hf.2 ⟨hr, hr1⟩ ⟨hr.trans (hrx.trans hxy), hy⟩ hs ht hst
    simp only [smul_eq_mul] at hc
    rw [hpt] at hc
    have hfy := mul_nonneg ht (hfn y ⟨hr.trans (hrx.trans hxy), hy⟩)
    dsimp [s] at hc
    have heq : f r * (y-x) / (y-r) = (y-x) / (y-r) * f r := by ring
    rw [heq]
    linarith
  have hc : ContinuousAt (fun y : ℝ => f r * (y - x) / (y - r)) 1 := by
    fun_prop (disch := linarith)
  apply le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto _ (𝓝[<] (1 : ℝ)) _)
  filter_upwards [(eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hxy hy
  exact hstep y hxy hy

private lemma regular_chord (F : Measure ℝ) [IsProbabilityMeasure F]
    (hreg : Regular F) (p q x : ℝ) (hp : 0 ≤ p)
    (hq0 : 0 < q) (hq1 : q < 1) (hqx : q < x) (hx : x < 1)
    (hq : q = 1 - rejection F p) :
    p * q * (1 - x) / (1 - q) ≤ revenueQuantile F x := by
  have hnn : ∀ z ∈ Ioo (0 : ℝ) 1, 0 ≤ revenueQuantile F z := by
    intro z hz
    exact mul_nonneg hz.1.le (quantile_nonneg F (1-z) (by linarith [hz.1]))
  have hstep : ∀ r, 0 < r → r < q →
      p * r * (1 - x) / (1 - r) ≤ revenueQuantile F x := by
    intro r hr hrq
    have hquant : p ≤ quantile F (1-r) :=
      quantile_above F (1-r) p (by linarith) (by rw [hq] at hrq; linarith)
    have hcurve : p * r ≤ revenueQuantile F r := by
      unfold revenueQuantile
      nlinarith [mul_le_mul_of_nonneg_left hquant hr.le]
    have hmul := mul_le_mul_of_nonneg_right hcurve (div_nonneg (sub_nonneg.mpr hx.le)
      (sub_nonneg.mpr (hrq.trans hq1).le))
    have hc := concave_chord_to_one (revenueQuantile F) hreg hnn r x hr (hrq.trans hqx) hx
    simp only [← mul_div_assoc] at hmul
    exact hmul.trans hc
  have hc : ContinuousAt (fun r : ℝ => p * r * (1 - x) / (1 - r)) q := by
    fun_prop (disch := linarith)
  apply le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto _ (𝓝[<] q) _)
  filter_upwards [(eventually_gt_nhds hq0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hr hrq
  exact hstep r hr hrq

theorem solution (F : Measure ℝ) (hF : ValidMarginal F) (hreg : Regular F)
    (p : ℝ) (hp : 0 < p) (hr : rejection F p ∈ Ioo (0 : ℝ) 1) :
    let a := p * (1 - rejection F p) / rejection F p
    0 < a ∧ rejection (triangularLaw a p) p = rejection F p ∧
      (∀ t : ℝ, 0 ≤ t → rejection F t ≤ rejection (triangularLaw a p) t) := by
  letI : IsProbabilityMeasure F := hF.1
  let r := rejection F p
  let q := 1-r
  let a := p*q/r
  have hq0 : 0 < q := sub_pos.mpr hr.2
  have hq1 : q < 1 := by dsimp [q,r]; linarith [hr.1]
  have ha : 0 < a := div_pos (mul_pos hp hq0) hr.1
  have hrnz : r ≠ 0 := hr.1.ne'
  have har : a*r = p*q := by dsimp [a]; field_simp [hrnz]
  have hq : q = 1 - rejection F p := rfl
  have hspec := triangular_law_specification a p ha hp
  have hcap : p / (p+a) = r := by
    apply (div_eq_iff (ne_of_gt (add_pos hp ha))).mpr
    dsimp [q] at har
    nlinarith
  change 0 < a ∧ rejection (triangularLaw a p) p = r ∧ _
  refine ⟨ha, ?_, ?_⟩
  · rw [hspec.2.2.1 p]
    simpa [triangularReject, not_le_of_gt hp] using hcap
  · intro t ht
    rw [hspec.2.2.1 t]
    by_cases ht0 : t ≤ 0
    · have htzero : t = 0 := le_antisymm ht0 ht
      subst t
      have hz : F (Iio (0 : ℝ)) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        exact hF.2.mono (fun _ hx => not_lt_of_ge hx)
      simp [triangularReject, rejection, hz]
    · by_cases htp : t ≤ p
      · simp only [triangularReject, if_neg ht0, if_pos htp]
        by_cases hteq : t = p
        · simpa [hteq, hcap, r]
        · have htp' : t < p := lt_of_le_of_ne htp hteq
          have htpos : 0 < t := lt_of_not_ge ht0
          have hta : 0 < t+a := add_pos htpos ha
          by_contra hbad
          have hbad' : t/(t+a) < rejection F t := lt_of_not_ge hbad
          let z := a/(t+a)
          have hz0 : 0 < z := div_pos ha hta
          have hz1 : z < 1 := (div_lt_one hta).mpr (by linarith)
          have hqz : q < z := by
            apply (lt_div_iff₀ hta).mpr
            have hqr : q+r=1 := by dsimp [q]; ring
            nlinarith [mul_lt_mul_of_pos_right htp' hq0]
          have htailz : 1 - rejection F t < z := by
            have hid : t/(t+a)+z=1 := by dsimp [z]; field_simp
            linarith
          obtain ⟨x, hxl, hxz⟩ := exists_between (max_lt hqz htailz)
          have hqx : q < x := (le_max_left _ _).trans_lt hxl
          have htx : 1-rejection F t < x := (le_max_right _ _).trans_lt hxl
          have hx1 : x < 1 := hxz.trans hz1
          have hx0 : 0 < x := hq0.trans hqx
          have hc := regular_chord F hreg p q x hp.le hq0 hq1 hqx hx1 hq
          have hquant : quantile F (1-x) ≤ t :=
            quantile_below F (1-x) t ht (by linarith [reject_le_cdf F t])
          have hup : revenueQuantile F x ≤ x*t :=
            mul_le_mul_of_nonneg_left hquant hx0.le
          have hcx : p*q*(1-x)/(1-q) ≤ x*t := hc.trans hup
          have hqr : 1-q=r := by dsimp [q]; ring
          rw [hqr] at hcx
          have hcx' := (div_le_iff₀ hr.1).mp hcx
          have hxz' := (lt_div_iff₀ hta).mp hxz
          have hmul := mul_lt_mul_of_pos_right hxz' hr.1
          nlinarith
      · simp [triangularReject, ht0, htp, (reject_bounds F t).2]
