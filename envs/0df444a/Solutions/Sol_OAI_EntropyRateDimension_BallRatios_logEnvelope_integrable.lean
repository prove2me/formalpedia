-- Prove2me | solution 1 for OAI.EntropyRateDimension.BallRatios.logEnvelope_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:13:45.619431+00:00
-- url     : https://prove2.me/submissions/1e7607bc-19ff-41da-8117-caadbb22e42f

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
theorem h41n_small_ratio : ∃ N : ℕ, ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞)
    (E : Set ℝ),
    (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
    ν E ≤ N*t*μ univ := by
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  refine ⟨N, fun μ ν t E hE => ?_⟩
  choose! r hr0 hr1 hrt using hE
  let q : Besicovitch.BallPackage E ℝ :=
    { c := fun x => x.1, r := fun x => r x.1, rpos := fun x => hr0 x.1 x.2, r_bound := 1,
      r_le := fun x => hr1 x.1 x.2 }
  obtain ⟨s, hsd, hcov⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hsd' : ∀ i, (s i).PairwiseDisjoint (fun j : E => Metric.closedBall (j:ℝ) (r j)) := hsd
  have hcount : ∀ i, (s i).Countable := by
    intro i
    have hd : (s i).PairwiseDisjoint (fun j : E => Metric.ball (j:ℝ) (r j)) :=
      (hsd' i).mono (fun j => Metric.ball_subset_closedBall)
    exact hd.countable_of_isOpen (fun j _ => Metric.isOpen_ball)
      (fun j _ => Metric.nonempty_ball.2 (hr0 j.1 j.2))
  have hEsub : E ⊆ ⋃ i, ⋃ j ∈ s i, Metric.closedBall (j:ℝ) (r j) := by
    intro x hx
    have h := hcov ⟨⟨x, hx⟩, rfl⟩
    simp only [Set.mem_iUnion] at h ⊢
    obtain ⟨i, j, hj, hxj⟩ := h
    exact ⟨i, j, hj, Metric.ball_subset_closedBall hxj⟩
  calc ν E ≤ ν (⋃ i, ⋃ j ∈ s i, Metric.closedBall (j:ℝ) (r j)) := measure_mono hEsub
    _ ≤ ∑ i, ν (⋃ j ∈ s i, Metric.closedBall (j:ℝ) (r j)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ∑' j : s i, ν (Metric.closedBall (j:ℝ) (r j)) :=
        Finset.sum_le_sum fun i _ => measure_biUnion_le _ (hcount i) _
    _ ≤ ∑ i, ∑' j : s i, t * μ (Metric.closedBall (j:ℝ) (r j)) :=
        Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun j => hrt j.1.1 j.1.2
    _ = ∑ i, t * μ (⋃ j ∈ s i, Metric.closedBall (j:ℝ) (r j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.tsum_mul_left, measure_biUnion (hcount i) (hsd' i)
          (fun _ _ => measurableSet_closedBall)]
    _ ≤ ∑ i : Fin N, t * μ Set.univ :=
        Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))
    _ = N * t * μ Set.univ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

theorem h41n_maximal_tail {N : ℕ}
    (hN : ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞) (E : Set ℝ),
      (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
      ν E ≤ N*t*μ univ)
    (μ ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ≥0∞) (ha : a ≠ 0) (hat : a ≠ ⊤) :
    ν {x | a < maximal μ ν x} ≤ N * a⁻¹ * μ univ := by
  apply hN μ ν a⁻¹ {x | a < maximal μ ν x}
  intro x hx
  simp only [Set.mem_setOf_eq, maximal, lt_iSup_iff] at hx
  obtain ⟨q, hq⟩ := hx
  refine ⟨q.val, q.property.1, q.property.2, ?_⟩
  rw [ENNReal.lt_div_iff_mul_lt (Or.inr hat) (Or.inl (measure_ne_top _ _))] at hq
  rw [mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl ha) (Or.inl hat), mul_comm]
  exact hq.le

theorem h41n_meas_cbE (μ : Measure ℝ) [IsFiniteMeasure μ] (q : ℝ) :
    Measurable (fun x => μ (Metric.closedBall x q)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ q} :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  exact measurable_measure_prodMk_left (ν := μ) hs

theorem solution (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (logEnvelope μ ν) ν := by
  obtain ⟨N, hN⟩ := h41n_small_ratio
  have hmeasM : Measurable (maximal μ ν) := by
    unfold maximal
    exact Measurable.iSup fun q => (h41n_meas_cbE μ _).div (h41n_meas_cbE ν _)
  have hmeas : Measurable (logEnvelope μ ν) := by
    unfold logEnvelope
    exact measurable_const.max (Real.measurable_log.comp hmeasM.ennreal_toReal)
  have hnn : ∀ x, 0 ≤ logEnvelope μ ν x := fun x => le_max_left _ _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  -- level sets
  have hlev : ∀ k : ℕ, ν {x | (k:ℝ) < logEnvelope μ ν x} ≤
      N * (ENNReal.ofReal (Real.exp k))⁻¹ * μ univ := by
    intro k
    refine le_trans (measure_mono ?_) (h41n_maximal_tail hN μ ν _
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    unfold logEnvelope at hx
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hlog : (k:ℝ) < Real.log (maximal μ ν x).toReal := by
      rcases le_or_gt (Real.log (maximal μ ν x).toReal) 0 with h | h
      · rw [max_eq_left h] at hx; linarith
      · rwa [max_eq_right h.le] at hx
    have hpos : 0 < (maximal μ ν x).toReal := by
      by_contra hc
      push_neg at hc
      have : (maximal μ ν x).toReal = 0 := le_antisymm hc ENNReal.toReal_nonneg
      rw [this, Real.log_zero] at hlog
      linarith
    have h1 : Real.exp k < (maximal μ ν x).toReal := by
      rwa [Real.lt_log_iff_exp_lt hpos] at hlog
    calc ENNReal.ofReal (Real.exp k) < ENNReal.ofReal (maximal μ ν x).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hpos).mpr h1
      _ ≤ maximal μ ν x := ENNReal.ofReal_toReal_le
  have hpt : ∀ x, ENNReal.ofReal (logEnvelope μ ν x) ≤
      ∑' k : ℕ, Set.indicator {x | (k:ℝ) < logEnvelope μ ν x} (fun _ => (1:ℝ≥0∞)) x := by
    intro x
    set m := ⌈logEnvelope μ ν x⌉₊
    calc ENNReal.ofReal (logEnvelope μ ν x) ≤ ENNReal.ofReal (m:ℝ) :=
          ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ = ∑ k ∈ Finset.range m, Set.indicator {x | (k:ℝ) < logEnvelope μ ν x}
            (fun _ => (1:ℝ≥0∞)) x := by
          rw [ENNReal.ofReal_natCast]
          rw [Finset.sum_congr rfl (g := fun _ => (1:ℝ≥0∞))]
          · simp
          · intro k hk
            rw [Finset.mem_range] at hk
            exact Set.indicator_of_mem (show (k:ℝ) < logEnvelope μ ν x from Nat.lt_ceil.mp hk)
              (fun _ => (1:ℝ≥0∞))
      _ ≤ _ := ENNReal.sum_le_tsum _
  have hq : ENNReal.ofReal (Real.exp (-1)) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by
      have := Real.exp_lt_exp.mpr (show (-1:ℝ) < 0 by norm_num)
      simpa using this)
  have hexp : ∀ k : ℕ, (ENNReal.ofReal (Real.exp k))⁻¹ = ENNReal.ofReal (Real.exp (-1)) ^ k := by
    intro k
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, ← ENNReal.ofReal_inv_of_pos
      (Real.exp_pos _), ← Real.exp_neg]
    congr 2
    ring
  calc ∫⁻ x, ENNReal.ofReal (logEnvelope μ ν x) ∂ν
      ≤ ∫⁻ x, ∑' k : ℕ, Set.indicator {x | (k:ℝ) < logEnvelope μ ν x} (fun _ => (1:ℝ≥0∞)) x ∂ν :=
        lintegral_mono hpt
    _ = ∑' k : ℕ, ν {x | (k:ℝ) < logEnvelope μ ν x} := by
        rw [lintegral_tsum (fun k => (measurable_const.indicator
          (measurableSet_lt measurable_const hmeas)).aemeasurable)]
        congr 1
        funext k
        rw [lintegral_indicator_const (measurableSet_lt measurable_const hmeas), one_mul]
    _ ≤ ∑' k : ℕ, N * (ENNReal.ofReal (Real.exp k))⁻¹ * μ univ := ENNReal.tsum_le_tsum hlev
    _ = N * μ univ * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ k := by
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext k
        rw [hexp]
        ring
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        apply ENNReal.mul_lt_top
        · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) (measure_lt_top _ _)
        · exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hq)

