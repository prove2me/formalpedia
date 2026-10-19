-- Prove2me | solution 1 for OAI.EntropyRateDimension.LocalMass.lower_dim_ge_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:37.771986+00:00
-- url     : https://prove2.me/submissions/04ab08ea-ff49-4ed4-9187-bb8f942ddedc

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
theorem h41n_meas_cbE (μ : Measure ℝ) [IsFiniteMeasure μ] (q : ℝ) :
    Measurable (fun x => μ (Metric.closedBall x q)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ q} :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  exact measurable_measure_prodMk_left (ν := μ) hs

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] {d : ℝ}
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

