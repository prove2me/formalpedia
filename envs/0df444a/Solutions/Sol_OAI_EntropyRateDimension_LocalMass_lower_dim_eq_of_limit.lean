-- Prove2me | solution 1 for OAI.EntropyRateDimension.LocalMass.lower_dim_eq_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:45:11.205438+00:00
-- url     : https://prove2.me/submissions/bd40ee88-1b40-45a0-b2b7-462243a1400f

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset

open OAI OAI.EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureEntropy
theorem h41n_evl (μ : Measure ℝ) [IsFiniteMeasure μ] {x e d : ℝ}
    (hx : x ∈ μ.support) (hde : d < e)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r) := by
  have hev := hlim.eventually (eventually_lt_nhds hde)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, h⟩ := hev
  refine ⟨min ε 1, lt_min hε one_pos, fun r hr hrR => ?_⟩
  have hrε : dist r 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    exact lt_of_lt_of_le hrR (min_le_left _ _)
  have h1 := h hrε (Set.mem_Ioi.mpr hr)
  have hlogr : 0 < -Real.log r :=
    neg_pos.mpr (Real.log_neg hr (lt_of_lt_of_le hrR (min_le_right _ _)))
  have hpos : 0 < μ.real (closedBall x r) := by
    have h0 := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
    exact ENNReal.toReal_pos h0.ne' (measure_ne_top _ _)
  rw [div_lt_iff₀ hlogr] at h1
  have h2 : Real.log (r^e) < Real.log (μ.real (closedBall x r)) := by
    rw [Real.log_rpow hr]; linarith
  exact ((Real.log_lt_log_iff (by positivity) hpos).mp h2).le


theorem h41n_meas_cb (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) :
    Measurable (fun x => μ.real (Metric.closedBall x q)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ q} :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have h := measurable_measure_prodMk_left (ν := μ) hs
  exact h.ennreal_toReal


theorem h41n_lums (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e η : ℝ} (he : 0 ≤ e) (hη : 0 < η)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ μ.real Eᶜ ≤ η ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
        (r/2)^e ≤ μ.real (ball x r) := by
  classical
  let E : ℕ → Set ℝ := fun k => {x | ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) < 1/((k:ℝ)+1) →
    (q:ℝ)^e ≤ μ.real (closedBall x q)}
  have hEm : ∀ k, MeasurableSet (E k) := by
    intro k
    simp only [E, Set.setOf_forall]
    refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le measurable_const (h41n_meas_cb μ q)
  have hmono : Monotone E := by
    intro k l hkl x hx q hq hql
    apply hx q hq (lt_of_lt_of_le hql _)
    apply one_div_le_one_div_of_le (by positivity)
    have : (k:ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ k, E k := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R, hR, h⟩ := hx
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hR
    exact Set.mem_iUnion.mpr ⟨k, fun q hq hqk => h q hq (hqk.trans hk)⟩
  have hnull : μ (⋂ k, (E k)ᶜ) = 0 := by
    rw [← Set.compl_iUnion]
    exact ae_iff.mp hcov
  have ht : Tendsto (fun k => μ (E k)ᶜ) atTop (𝓝 (μ (⋂ k, (E k)ᶜ))) :=
    tendsto_measure_iInter_atTop (fun k => (hEm k).compl.nullMeasurableSet)
      (fun k l hkl => Set.compl_subset_compl.mpr (hmono hkl)) ⟨0, measure_ne_top _ _⟩
  rw [hnull] at ht
  have hev := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨E k, hEm k, ?_, 2/((k:ℝ)+1), by positivity, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal hη.le hk.le
  · intro x hx r hr hrR
    have h1 : r/2 < min r (1/((k:ℝ)+1)) := by
      apply lt_min (by linarith)
      have : r/2 < 1/((k:ℝ)+1) := by
        rw [lt_div_iff₀ (by positivity)]
        rw [lt_div_iff₀ (by positivity)] at hrR
        linarith
      exact this
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
    have hq0 : 0 < (q:ℝ) := by linarith
    calc (r/2)^e ≤ (q:ℝ)^e := Real.rpow_le_rpow (by linarith) hq1.le he
      _ ≤ μ.real (closedBall x q) := hx q hq0 (lt_of_lt_of_le hq2 (min_le_right _ _))
      _ ≤ μ.real (Metric.ball x r) :=
          measureReal_mono (Metric.closedBall_subset_ball (lt_of_lt_of_le hq2 (min_le_left _ _)))


theorem h41n_meas_cbE (μ : Measure ℝ) [IsFiniteMeasure μ] (q : ℝ) :
    Measurable (fun x => μ (Metric.closedBall x q)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ q} :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  exact measurable_measure_prodMk_left (ν := μ) hs


theorem h41n_ldge (μ : Measure ℝ) [IsProbabilityMeasure μ] {d : ℝ}
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    ENNReal.ofReal d ≤ lowerHausdorffDimension μ := by
  unfold lowerHausdorffDimension
  refine le_iInf fun E => le_iInf fun hE => le_iInf fun hpos => ?_
  apply le_of_forall_lt
  intro c hc
  have hct : c ≠ ⊤ := ne_top_of_lt hc
  have hcr : c.toReal < d := by rwa [ENNReal.lt_ofReal_iff_toReal_lt hct] at hc
  obtain ⟨d', h1, hd'd⟩ := exists_between hcr
  have hcd' : c < ENNReal.ofReal d' := by rwa [ENNReal.lt_ofReal_iff_toReal_lt hct]
  have hd'0 : 0 < d' := lt_of_le_of_lt ENNReal.toReal_nonneg h1
  refine hcd'.trans_le ?_
  -- uniform sets
  let F : ℕ → Set ℝ := fun k => E ∩ {x | ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) < 1/((k:ℝ)+1) →
    μ (closedBall x q) ≤ ENNReal.ofReal ((q:ℝ)^d')}
  have hFm : ∀ k, MeasurableSet (F k) := by
    intro k
    refine hE.inter ?_
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (h41n_meas_cbE μ q) measurable_const
  have hcov : ∀ᵐ x ∂μ, x ∈ E → x ∈ ⋃ k, F k := by
    filter_upwards [hlim] with x hx hxE
    have hev := hx.eventually (eventually_gt_nhds hd'd)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, h⟩ := hev
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min hε one_pos)
    refine Set.mem_iUnion.mpr ⟨k, hxE, fun q hq hqk => ?_⟩
    have hqε : (q:ℝ) < min ε 1 := hqk.trans hk
    have hr := h (show dist (q:ℝ) 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_pos hq]; exact lt_of_lt_of_le hqε (min_le_left _ _))
      (Set.mem_Ioi.mpr hq)
    have hlogr : 0 < -Real.log q :=
      neg_pos.mpr (Real.log_neg hq (lt_of_lt_of_le hqε (min_le_right _ _)))
    rw [lt_div_iff₀ hlogr] at hr
    have hle : μ.real (closedBall x q) ≤ (q:ℝ)^d' := by
      rcases eq_or_lt_of_le (measureReal_nonneg (μ := μ) (s := closedBall x q)) with h0 | h0
      · rw [← h0]; positivity
      · have : Real.log (μ.real (closedBall x q)) < Real.log ((q:ℝ)^d') := by
          rw [Real.log_rpow hq]; linarith
        exact ((Real.log_lt_log_iff h0 (by positivity)).mp this).le
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (closedBall x (q:ℝ)))]
    exact ENNReal.ofReal_le_ofReal hle
  have hEU : μ E ≤ μ (⋃ k, F k) := measure_mono_ae (hcov.mono fun x hx => hx)
  obtain ⟨k, hk⟩ : ∃ k, 0 < μ (F k) := by
    by_contra hc
    push_neg at hc
    have : μ (⋃ k, F k) = 0 := measure_iUnion_null fun k => le_antisymm (hc k) bot_le
    rw [this] at hEU
    exact absurd (le_antisymm hEU bot_le) hpos.ne'
  -- Hausdorff measure bound
  set C : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^d') with hC
  have hC0 : C ≠ 0 := by rw [hC]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  set ε0 : ℝ≥0∞ := ENNReal.ofReal (1/(2*((k:ℝ)+1))) with hε0
  have hε0pos : 0 < ε0 := ENNReal.ofReal_pos.mpr (by positivity)
  have hbound : ∀ s : Set ℝ, Metric.ediam s ≤ ε0 →
      μ.restrict (F k) s ≤ C * Metric.ediam s ^ d' := by
    intro s hs
    rw [Measure.restrict_apply' (hFm k)]
    rcases (s ∩ F k).eq_empty_or_nonempty with he | ⟨x, hxs, hxF⟩
    · rw [he]; simp
    have hδt : Metric.ediam s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
    have hball : ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) < 1/((k:ℝ)+1) → Metric.ediam s < ENNReal.ofReal q →
        μ (s ∩ F k) ≤ ENNReal.ofReal ((q:ℝ)^d') := by
      intro q hq hqk hδq
      refine le_trans (measure_mono ?_) (hxF.2 q hq hqk)
      intro y hy
      rw [Metric.mem_closedBall]
      have h1 := Metric.edist_le_ediam_of_mem hy.1 hxs
      rw [edist_dist] at h1
      have h2 := lt_of_le_of_lt h1 hδq
      exact ((ENNReal.ofReal_lt_ofReal_iff hq).mp h2).le
    rcases eq_or_ne (Metric.ediam s) 0 with h0 | h0
    · -- zero diameter: mass is zero
      rw [h0, ENNReal.zero_rpow_of_pos hd'0, mul_zero, nonpos_iff_eq_zero]
      apply le_antisymm _ bot_le
      apply ENNReal.le_of_forall_pos_le_add
      intro η hη _
      rw [show (⊥:ℝ≥0∞) = 0 from rfl, zero_add]
      have hη' : (0:ℝ) < (η:ℝ) ^ (1/d') := Real.rpow_pos_of_pos (by exact_mod_cast hη) _
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hη' (by positivity : (0:ℝ) < 1/((k:ℝ)+1)))
      refine le_trans (hball q hq1 (lt_of_lt_of_le hq2 (min_le_right _ _))
        (by rw [h0]; exact ENNReal.ofReal_pos.mpr hq1)) ?_
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      have : (q:ℝ)^d' ≤ ((η:ℝ)^(1/d'))^d' :=
        Real.rpow_le_rpow hq1.le (lt_of_lt_of_le hq2 (min_le_left _ _)).le hd'0.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hd'0.ne', Real.rpow_one] at this
    · set a := (Metric.ediam s).toReal with ha
      have hapos : 0 < a := ENNReal.toReal_pos h0 hδt
      have hδ : Metric.ediam s = ENNReal.ofReal a := (ENNReal.ofReal_toReal hδt).symm
      have ha2 : 2 * a ≤ 1/((k:ℝ)+1) := by
        have : ENNReal.ofReal a ≤ ε0 := hδ ▸ hs
        rw [hε0, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
        have e : 1/(2*((k:ℝ)+1)) = (1/((k:ℝ)+1))/2 := by field_simp
        rw [e] at this
        linarith
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show a < 2*a by linarith)
      have hq0 : (0:ℝ) < q := by linarith
      refine le_trans (hball q hq0 (by linarith) (by rw [hδ]; exact (ENNReal.ofReal_lt_ofReal_iff hq0).mpr hq1)) ?_
      rw [hδ, ENNReal.ofReal_rpow_of_nonneg hapos.le hd'0.le, hC, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.mul_rpow (by norm_num) hapos.le]
      exact Real.rpow_le_rpow hq0.le hq2.le hd'0.le
  have hle : C⁻¹ • μ.restrict (F k) ≤ μH[d'] := by
    apply Measure.le_hausdorffMeasure d' _ ε0 hε0pos
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul]
    calc C⁻¹ * μ.restrict (F k) s ≤ C⁻¹ * (C * Metric.ediam s ^ d') :=
          mul_le_mul' le_rfl (hbound s hs)
      _ = Metric.ediam s ^ d' := by rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul]
  have hHpos : μH[d'] (F k) ≠ 0 := by
    have h1 := hle (F k)
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self] at h1
    intro h0
    rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact (ENNReal.inv_ne_zero.mpr hCt) h
    · exact hk.ne' h
  have hd'eq : ((d'.toNNReal : ℝ)) = d' := Real.coe_toNNReal _ hd'0.le
  have := le_dimH_of_hausdorffMeasure_ne_zero (d := d'.toNNReal) (by rwa [hd'eq])
  exact this.trans (dimH_mono (Set.inter_subset_left))


theorem h41n_card_q2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : Finset ℤ) (x : ℤ → ℝ)
    (r q : ℝ) (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → 2*r ≤ dist (x i) (x j))
    (hq : ∀ i ∈ t, q ≤ μ.real (Metric.ball (x i) r)) : (t.card : ℝ) * q ≤ 1 := by
  have hpd : (↑t : Set ℤ).PairwiseDisjoint (fun i => Metric.ball (x i) r) := by
    intro i hi j hj hij
    exact Metric.ball_disjoint_ball (by linarith [hdisj i hi j hj hij])
  calc (t.card : ℝ) * q = ∑ i ∈ t, q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ t, μ.real (Metric.ball (x i) r) := Finset.sum_le_sum hq
    _ = μ.real (⋃ i ∈ t, Metric.ball (x i) r) :=
        (measureReal_biUnion_finset hpd (fun _ _ => Metric.isOpen_ball.measurableSet)).symm
    _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
    _ = 1 := by simp


theorem h41n_good_labels (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s u q : ℝ} (hs : 0 < s) (a : Finset ℤ) (x : ℤ → ℝ)
    (hx : ∀ i ∈ a, label s u (x i)=i)
    (hq : ∀ i ∈ a, q ≤ μ.real (Metric.ball (x i) (s/2))) :
    (a.card : ℝ)*q ≤ 3 := by
  classical
  have key : ∀ t ⊆ a, (∀ i ∈ t, ∀ j ∈ t, i ≠ j → i + 2 ≤ j ∨ j + 2 ≤ i) →
      (t.card : ℝ) * q ≤ 1 := by
    intro t ht hsep
    apply h41n_card_q2 μ t x (s/2) q _ (fun i hi => hq i (ht hi))
    have sep1 : ∀ i ∈ t, ∀ j ∈ t, i + 2 ≤ j → s ≤ x j - x i := by
      intro i hi j hj h
      have hfi := hx i (ht hi)
      have hfj := hx j (ht hj)
      simp only [label, Int.floor_eq_iff] at hfi hfj
      have h' : (i:ℝ) + 2 ≤ j := by exact_mod_cast h
      have h1 : 1 ≤ x j / s - x i / s := by linarith
      have e : x j - x i = s * (x j / s - x i / s) := by field_simp
      rw [e]; nlinarith
    intro i hi j hj hij
    rw [Real.dist_eq]
    rcases hsep i hi j hj hij with h | h
    · have := sep1 i hi j hj h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have := sep1 j hj i hi h
      rw [abs_of_nonneg (by linarith)]; linarith
  have h1 := key (a.filter (fun i => Even i)) (Finset.filter_subset _ _) (by
    intro i hi j hj hij
    simp only [Finset.mem_filter, Int.even_iff] at hi hj
    omega)
  have h2 := key (a.filter (fun i => ¬ Even i)) (Finset.filter_subset _ _) (by
    intro i hi j hj hij
    simp only [Finset.mem_filter, Int.not_even_iff] at hi hj
    omega)
  have hc := Finset.card_filter_add_card_filter_not (s := a) (fun i => Even i)
  have hc' : (a.card : ℝ) = ((a.filter (fun i => Even i)).card : ℝ) +
      ((a.filter (fun i => ¬ Even i)).card : ℝ) := by exact_mod_cast hc.symm
  rw [hc', add_mul]
  linarith


theorem h41n_dimle (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) {B e R : ℝ} (he : 0 ≤ e) (hR : 0 < R)
    (hE : E ⊆ Icc (-B) B)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
      (r/2)^e ≤ μ.real (ball x r)) : dimH E ≤ ENNReal.ofReal e := by
  classical
  -- scales
  let δ : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hδR : ∀ᶠ n in atTop, δ n < R := hδlim.eventually (eventually_lt_nhds hR)
  let cell : ℕ → ℤ → Set ℝ := fun n j => E ∩ {x | label (δ n) 0 x = j}
  let J : ℕ → Finset ℤ := fun n =>
    (Finset.Icc ⌊-B/(δ n) + 0⌋ ⌊B/(δ n) + 0⌋).filter (fun j => (cell n j).Nonempty)
  let t : ∀ n : ℕ, (J n) → Set ℝ := fun n i => cell n i.1
  have hdiam : ∀ n (i : J n), Metric.ediam (t n i) ≤ ENNReal.ofReal (δ n) := by
    intro n i
    apply Metric.ediam_le
    intro x hx y hy
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hx2 : label (δ n) 0 x = i.1 := hx.2
    have hy2 : label (δ n) 0 y = i.1 := hy.2
    simp only [label, Int.floor_eq_iff] at hx2 hy2
    have h1 : x / δ n - y / δ n < 1 := by linarith
    have h2 : y / δ n - x / δ n < 1 := by linarith
    have hδn : δ n ≠ 0 := (hδpos n).ne'
    have e1 : x - y = δ n * (x / δ n - y / δ n) := by field_simp
    rw [Real.dist_eq, abs_le]
    constructor
    · have := hδpos n; nlinarith
    · have := hδpos n; nlinarith
  have hcover : ∀ n, E ⊆ ⋃ i, t n i := by
    intro n x hx
    have hxB := hE hx
    rw [Set.mem_iUnion]
    have hmem : label (δ n) 0 x ∈ J n := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨x, hx, rfl⟩⟩
      · apply Int.floor_mono
        have := div_le_div_of_nonneg_right hxB.1 (hδpos n).le
        linarith
      · apply Int.floor_mono
        have := div_le_div_of_nonneg_right hxB.2 (hδpos n).le
        linarith
    exact ⟨⟨_, hmem⟩, hx, rfl⟩
  have hcard : ∀ᶠ n in atTop, ((J n).card : ℝ) * (δ n / 4)^e ≤ 3 := by
    filter_upwards [hδR] with n hn
    let xf : ℤ → ℝ := fun j => if h : (cell n j).Nonempty then h.choose else 0
    have hxf : ∀ j ∈ J n, xf j ∈ cell n j := by
      intro j hj
      have h : (cell n j).Nonempty := (Finset.mem_filter.mp hj).2
      simp only [xf, dif_pos h]
      exact h.choose_spec
    have := h41n_good_labels μ (hδpos n) (J n) xf (fun j hj => (hxf j hj).2)
      (fun j hj => by
        have h1 := hball (xf j) (hxf j hj).1 (δ n / 2) (by linarith [hδpos n]) (by linarith [hδpos n])
        rwa [show δ n / 2 / 2 = δ n / 4 by ring] at h1)
    exact this
  have hsum : ∀ᶠ n in atTop, ∑ i, Metric.ediam (t n i) ^ e ≤ ENNReal.ofReal (3 * 4^e) := by
    filter_upwards [hcard] with n hn
    calc ∑ i, Metric.ediam (t n i) ^ e ≤ ∑ _i : J n, ENNReal.ofReal (δ n) ^ e :=
          Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hdiam n i) he
      _ = ENNReal.ofReal ((J n).card * (δ n)^e) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
            ENNReal.ofReal_rpow_of_nonneg (hδpos n).le he, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (3 * 4^e) := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.div_rpow (hδpos n).le (by norm_num)] at hn
          have h4 : (0:ℝ) < 4^e := by positivity
          rw [← mul_div_assoc, div_le_iff₀ h4] at hn
          linarith
  have hH : μH[e] E ≤ ENNReal.ofReal (3 * 4^e) := by
    refine le_trans (Measure.hausdorffMeasure_le_liminf_sum e E (fun n => ENNReal.ofReal (δ n))
      (by simpa using ENNReal.tendsto_ofReal hδlim) t
      (Filter.Eventually.of_forall fun n i => hdiam n i)
      (Filter.Eventually.of_forall hcover)) ?_
    exact Filter.liminf_le_of_frequently_le' hsum.frequently
  have he' : ((e.toNNReal : ℝ)) = e := Real.coe_toNNReal _ he
  apply dimH_le_of_hausdorffMeasure_ne_top
  rw [he']
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : CompactlyCarried μ) {d : ℝ} (hd : 0 ≤ d)
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    lowerHausdorffDimension μ = ENNReal.ofReal d := by
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hlt
    rcases eq_or_ne c ⊤ with hct | hct
    · rw [hct]; exact le_top
    have hcr : d < c.toReal := by
      rwa [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd, ENNReal.ofReal_toReal hct]
    obtain ⟨e, hde, hec⟩ := exists_between hcr
    have he0 : 0 ≤ e := hd.trans hde.le
    have hloc : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
        r^e ≤ μ.real (closedBall x r) := by
      filter_upwards [hlim, (Measure.support_mem_ae : μ.support ∈ ae μ)] with x hx hxs
      exact h41n_evl μ hxs hde hx
    obtain ⟨E, hEm, hEc, R, hR, hER⟩ := h41n_lums μ he0 (by norm_num : (0:ℝ) < 1/2) hloc
    obtain ⟨B, hB0, hB⟩ := hc
    set E' := E ∩ Set.Icc (-B) B
    have hE'm : MeasurableSet E' := hEm.inter measurableSet_Icc
    have hE'pos : 0 < μ E' := by
      rw [pos_iff_ne_zero]
      intro h0
      have h1 : μ E'ᶜ = 1 := by rw [prob_compl_eq_one_sub hE'm, h0, tsub_zero]
      have h2 : μ E'ᶜ ≤ μ Eᶜ + μ (Set.Icc (-B) B)ᶜ := by
        rw [Set.compl_inter]; exact measure_union_le _ _
      rw [hB, add_zero, h1] at h2
      have h3 : μ Eᶜ ≤ ENNReal.ofReal (1/2) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ Eᶜ)]
        exact ENNReal.ofReal_le_ofReal hEc
      have h4 : ENNReal.ofReal (1/2 : ℝ) < 1 := by
        rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by norm_num)
      exact absurd (h2.trans h3) (not_le.mpr h4)
    have hdim : dimH E' ≤ ENNReal.ofReal e :=
      h41n_dimle μ E' he0 hR Set.inter_subset_right (fun x hx r hr hrR => hER x hx.1 r hr hrR)
    calc lowerHausdorffDimension μ ≤ dimH E' := by
          unfold lowerHausdorffDimension
          exact iInf_le_of_le E' (iInf_le_of_le hE'm (iInf_le_of_le hE'pos le_rfl))
      _ ≤ ENNReal.ofReal e := hdim
      _ ≤ c := by
          rw [← ENNReal.ofReal_toReal hct]
          exact ENNReal.ofReal_le_ofReal hec.le
  · exact h41n_ldge μ hlim

