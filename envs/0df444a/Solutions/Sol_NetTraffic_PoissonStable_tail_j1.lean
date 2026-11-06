-- Prove2me | solution 1 for NetTraffic.PoissonStable.tail_j1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:06:53.211854+00:00
-- url     : https://prove2.me/submissions/966b05e9-0ce0-41ae-8fa8-23108d7e667b

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open NetTraffic.PoissonStable

namespace Sol_tj1

noncomputable def G : Measure ℝ := paretoMeasure 1 (3 / 2)

instance : IsProbabilityMeasure G := isProbabilityMeasure_paretoMeasure one_pos (by norm_num)

noncomputable def F0 : Measure ℝ := (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • G

instance : IsProbabilityMeasure F0 :=
  ⟨by simp [F0, measure_univ]; exact ENNReal.inv_two_add_inv_two⟩

lemma G_Ioi (y : ℝ) (hy : 1 ≤ y) : G (Ioi y) = ENNReal.ofReal (y ^ (-(3 / 2 : ℝ))) := by
  have hy0 : 0 < y := by linarith
  rw [G, paretoMeasure, withDensity_apply _ measurableSet_Ioi]
  have h1 : ∫⁻ x in Ioi y, paretoPDF 1 (3 / 2) x =
      ∫⁻ x in Ioi y, ENNReal.ofReal ((3 / 2) * x ^ (-(5 / 2 : ℝ))) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [paretoPDF_of_le (le_trans hy (le_of_lt hx))]
    norm_num
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hy0]
    norm_num
    ring
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hy0).const_mul _
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have : 0 < x := lt_trans hy0 hx
    simp only [Pi.zero_apply]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg this.le _)

lemma F0_apply (s : Set ℝ) : F0 s = 2⁻¹ * Measure.dirac 0 s + 2⁻¹ * G s := by
  simp [F0]

lemma Fbar_F0 (y : ℝ) (hy : 1 ≤ y) : Fbar F0 y = 2⁻¹ * y ^ (-(3 / 2 : ℝ)) := by
  unfold Fbar
  rw [measureReal_def, F0_apply, G_Ioi y hy]
  have : Measure.dirac (0 : ℝ) (Ioi y) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Ioi]
    simp; linarith
  rw [this, mul_zero, zero_add, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg (by linarith) _)]
  simp

lemma F0_Ioi_zero : F0 (Ioi 0) ≤ 2⁻¹ := by
  rw [F0_apply]
  have : Measure.dirac (0 : ℝ) (Ioi 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Ioi]; simp
  rw [this, mul_zero, zero_add]
  calc 2⁻¹ * G (Ioi 0) ≤ 2⁻¹ * 1 := mul_le_mul_right (prob_le_one) _
    _ = 2⁻¹ := mul_one _

lemma F0_Iio : F0 (Iio 0) = 0 := by
  rw [F0_apply]
  have : Measure.dirac (0 : ℝ) (Iio 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iio]; simp
  have h2 : G (Iio 0) = 0 := by
    rw [G, paretoMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_paretoPDF_of_le (by norm_num)
  rw [this, h2]; simp

lemma Lval (x : ℝ) (hx : 1 ≤ x) : x ^ (3 / 2 : ℝ) * Fbar F0 x = 2⁻¹ := by
  rw [Fbar_F0 x hx, Real.rpow_neg (by linarith)]
  have : 0 < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  field_simp

lemma heavy : HeavyTail F0 (3 / 2) where
  nonneg := F0_Iio
  one_lt := by norm_num
  lt_two := by norm_num
  slowlyVarying := by
    constructor
    · filter_upwards [eventually_ge_atTop 1] with x hx
      rw [Lval x hx]; norm_num
    · intro c hc
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (max 1 (1 / c))] with x hx
      have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
      have hcx : 1 ≤ c * x := by
        have : 1 / c ≤ x := le_trans (le_max_right _ _) hx
        rw [div_le_iff₀ hc] at this; linarith
      rw [Lval x hx1, Lval (c * x) hcx]; norm_num

lemma Fbar_anti : Antitone (Fbar F0) := by
  intro x y hxy
  unfold Fbar
  exact measureReal_mono (Set.Ioi_subset_Ioi hxy)

lemma b_le (s y : ℝ) (hy : 0 < y) (h : s * Fbar F0 y ≤ 1) : b F0 s ≤ y :=
  csInf_le ⟨0, fun x hx => hx.1.le⟩ ⟨hy, h⟩

lemma b_nonneg (s : ℝ) : 0 ≤ b F0 s := Real.sInf_nonneg (fun x hx => hx.1.le)

lemma cond1 : Condition1 F0 (fun _ => 1) := by
  unfold Condition1
  have hlim : Tendsto (fun T : ℝ => T ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    exact div_nonneg (b_nonneg _) hT.le
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : 0 < T := by linarith
    have hy1 : 1 ≤ T ^ (2 / 3 : ℝ) := Real.one_le_rpow hT (by norm_num)
    have hb : b F0 (1 * T) ≤ T ^ (2 / 3 : ℝ) := by
      apply b_le _ _ (by linarith)
      rw [Fbar_F0 _ hy1, ← Real.rpow_mul hT0.le]
      norm_num
      rw [Real.rpow_neg_one]
      field_simp
      norm_num
    calc b F0 (1 * T) / T ≤ T ^ (2 / 3 : ℝ) / T := div_le_div_of_nonneg_right hb hT0.le
      _ = T ^ (-(1 / 3 : ℝ)) := by
        rw [← Real.rpow_sub_one hT0.ne']; norm_num

end Sol_tj1

open Sol_tj1 in
theorem solution : ¬ (∀ (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ), HeavyTail Fon α →
    ∀ (lam : ℝ → ℝ), (∀ T, 0 < lam T) → Monotone lam → Condition1 Fon lam →
    ∀ x : ℝ, 0 < x →
      Tendsto (fun T => lam T * T * (j1Law Fon T).real (Set.Ioi (b Fon (lam T * T) * x)))
        atTop (𝓝 (x ^ (-α)))) := by
  intro H
  have h := H F0 (3 / 2) heavy (fun _ => 1) (fun _ => one_pos) monotone_const cond1 1 one_pos
  simp only [one_mul, mul_one, Real.one_rpow] at h
  -- the eventual lower bound `5/4`
  have hw : Tendsto (fun T : ℝ => T * Fbar F0 (T / 4)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => 2 * (T / 4) ^ (-(1 / 2 : ℝ))) atTop (𝓝 (2 * 0)) :=
      ((tendsto_rpow_neg_atTop (by norm_num)).comp
        (tendsto_id.atTop_div_const (by norm_num))).const_mul 2
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with T hT
    have hT4 : 1 ≤ T / 4 := by linarith
    have hpos : 0 < T / 4 := by linarith
    rw [Fbar_F0 _ hT4]
    have e : (T / 4) ^ (-(1 / 2 : ℝ)) = (T / 4) ^ (1 : ℝ) * (T / 4) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hpos]; norm_num
    rw [e, Real.rpow_one]
    ring
  have hev : ∀ᶠ T in atTop, (5 / 4 : ℝ) ≤ T * (j1Law F0 T).real (Ioi (b F0 T)) := by
    filter_upwards [hw.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6)),
      eventually_ge_atTop 4] with T hwT hT
    have hT0 : 0 < T := by linarith
    set bb := b F0 T with hbb
    have hb0 : 0 ≤ bb := b_nonneg _
    -- T F̄(bb) ≥ 1
    have hTb : 1 ≤ T * Fbar F0 bb := by
      have hy1 : 1 ≤ (T / 2) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have hval : T * Fbar F0 ((T / 2) ^ (2 / 3 : ℝ)) = 1 := by
        rw [Fbar_F0 _ hy1, ← Real.rpow_mul (by linarith)]
        norm_num
        rw [Real.rpow_neg_one]
        field_simp
      have hle : bb ≤ (T / 2) ^ (2 / 3 : ℝ) := b_le _ _ (by linarith) hval.le
      have := Fbar_anti hle
      nlinarith
    -- bb ≤ T/4
    have hbc : bb ≤ T / 4 := b_le _ _ (by linarith) (by linarith)
    -- F0.real (Ioc bb (T/4)) = F̄(bb) - F̄(T/4)
    have hIoc : F0.real (Ioc bb (T / 4)) = Fbar F0 bb - Fbar F0 (T / 4) := by
      unfold Fbar
      rw [← Ioc_union_Ioi_eq_Ioi hbc, measureReal_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi]
      ring
    have hIocT : 5 / 6 ≤ T * F0.real (Ioc bb (T / 4)) := by
      rw [hIoc]; nlinarith
    -- measures
    set μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod F0 with hμ
    have hm : μ (R1 T) ≤ ENNReal.ofReal T * 2⁻¹ := by
      calc μ (R1 T) ≤ μ (Ioc 0 T ×ˢ Ioi 0) := by
            apply measure_mono
            intro p hp
            exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2.1⟩
        _ = ENNReal.ofReal T * F0 (Ioi 0) := by
            rw [hμ, Measure.prod_prod, Real.volume_Ioc, sub_zero]
        _ ≤ ENNReal.ofReal T * 2⁻¹ := mul_le_mul_right F0_Ioi_zero _
    have hn : ENNReal.ofReal (3 * T / 4) * F0 (Ioc bb (T / 4)) ≤
        μ (Prod.snd ⁻¹' Ioi bb ∩ R1 T) := by
      calc ENNReal.ofReal (3 * T / 4) * F0 (Ioc bb (T / 4))
          = μ (Ioc 0 (3 * T / 4) ×ˢ Ioc bb (T / 4)) := by
            rw [hμ, Measure.prod_prod, Real.volume_Ioc, sub_zero]
        _ ≤ μ (Prod.snd ⁻¹' Ioi bb ∩ R1 T) := by
            apply measure_mono
            rintro ⟨s, y⟩ ⟨⟨hs1, hs2⟩, hy1, hy2⟩
            refine ⟨hy1, hs1, by linarith, by linarith, by linarith⟩
    have hnm : μ (Prod.snd ⁻¹' Ioi bb ∩ R1 T) ≤ μ (R1 T) := measure_mono inter_subset_right
    have hmfin : μ (R1 T) ≠ ∞ := ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top]) hm
    have hnfin : μ (Prod.snd ⁻¹' Ioi bb ∩ R1 T) ≠ ∞ := ne_top_of_le_ne_top hmfin hnm
    have hj : (j1Law F0 T).real (Ioi bb) =
        (μ (Prod.snd ⁻¹' Ioi bb ∩ R1 T)).toReal / (μ (R1 T)).toReal := by
      rw [measureReal_def, j1Law, Measure.smul_apply, smul_eq_mul,
        Measure.map_apply measurable_snd measurableSet_Ioi,
        Measure.restrict_apply (measurable_snd measurableSet_Ioi), ENNReal.toReal_mul,
        ENNReal.toReal_inv, ← hμ]
      ring
    have hmR : (μ (R1 T)).toReal ≤ T / 2 := by
      have := ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hm
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hT0.le] at this
      simpa [div_eq_mul_inv] using this
    have hnR : 3 * T / 4 * F0.real (Ioc bb (T / 4)) ≤ (μ (Prod.snd ⁻¹' Ioi bb ∩ R1 T)).toReal := by
      have := ENNReal.toReal_mono hnfin hn
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ← measureReal_def] at this
    have hpos1 : 0 < 3 * T / 4 * F0.real (Ioc bb (T / 4)) := by
      have : 0 < F0.real (Ioc bb (T / 4)) := by nlinarith
      positivity
    have hmpos : 0 < (μ (R1 T)).toReal :=
      lt_of_lt_of_le (lt_of_lt_of_le hpos1 hnR) (ENNReal.toReal_mono hmfin hnm)
    rw [hj, mul_div_assoc', le_div_iff₀ hmpos]
    have h3 : T * (3 * T / 4 * F0.real (Ioc bb (T / 4))) ≤
        T * (μ (Prod.snd ⁻¹' Ioi bb ∩ R1 T)).toReal := mul_le_mul_of_nonneg_left hnR hT0.le
    nlinarith
  have := ge_of_tendsto h hev
  norm_num at this
