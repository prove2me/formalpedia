-- Prove2me | solution 1 for MartingaleHT.InfiniteServer.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:46:43.150051+00:00
-- url     : https://prove2.me/submissions/eabb52a4-19cc-47f6-930e-4d8548693b98

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit
import Theorems.Thm_MartingaleHT_InfiniteServer_lemma_3_3
import Theorems.Thm_MartingaleHT_InfiniteServer_lemma_4_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling ErlangA.Diffusion
open MartingaleHT.InfiniteServer

/-- Mean of the Poisson law: `∑ j · e^{-r} r^j / j! = r`. -/
lemma mht62_hasSum_mean (r : ℝ≥0) :
    HasSum (fun j : ℕ => (j : ℝ) * (Real.exp (-r) * (r:ℝ) ^ j / (j.factorial))) r := by
  have H := (hasSum_one_poissonMeasure r).mul_left (r:ℝ)
  rw [mul_one] at H
  have e : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * (Real.exp (-r) * (r:ℝ) ^ (n + 1) / ((n + 1).factorial))
      = (r:ℝ) * (Real.exp (-r) * (r:ℝ) ^ n / (n.factorial)) := by
    intro n
    rw [Nat.factorial_succ]
    push_cast
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have H2 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      (Real.exp (-r) * (r:ℝ) ^ (n + 1) / ((n + 1).factorial)))
      ((r:ℝ) - ∑ i ∈ Finset.range 1, (i : ℝ) * (Real.exp (-r) * (r:ℝ) ^ i / (i.factorial))) := by
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
    simp only [e]
    exact H
  exact (hasSum_nat_add_iff' 1).1 H2

/-- Markov-type tail bound for a rate-one Poisson process: `P(N(s) > a) ≤ s / a`. -/
lemma mht62_poisson_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → ℝ → ℝ)
    (hN : IsPoissonProcess P N 1) (s : ℝ) (hs : 0 ≤ s) (a : ℝ) (ha : 0 < a) :
    P {ω | a < N ω s} ≤ ENNReal.ofReal (s / a) := by
  set r : ℝ≥0 := (1 * (s - 0)).toNNReal with hr
  have hrs : (r : ℝ) = s := by rw [hr]; simp [hs]
  set p : ℕ → ℝ := fun j => Real.exp (-r) * (r:ℝ) ^ j / (j.factorial)
  have hp0 : ∀ j, 0 ≤ p j := fun j => by positivity
  have hlaw : ∀ j : ℕ, P {ω | N ω s - N ω 0 = j} = ENNReal.ofReal (p j) := by
    intro j
    rw [hN.law 0 s le_rfl hs j, poissonMeasure_singleton]
  have hset : {ω | a < N ω s} ⊆ ⋃ j : ℕ, {ω | N ω s - N ω 0 = j ∧ a < j} := by
    intro ω hω
    obtain ⟨m, hm⟩ := hN.nat_valued ω s hs
    refine Set.mem_iUnion.2 ⟨m, ?_, ?_⟩
    · simp [hN.zero ω, hm]
    · have : a < N ω s := hω
      rwa [hm] at this
  have hterm : ∀ j : ℕ, P {ω | N ω s - N ω 0 = j ∧ a < j} ≤ ENNReal.ofReal (j / a * p j) := by
    intro j
    by_cases hj : a < j
    · have hsub : {ω | N ω s - N ω 0 = j ∧ a < j} ⊆ {ω | N ω s - N ω 0 = j} :=
        fun ω hω => hω.1
      refine le_trans (measure_mono hsub) ?_
      rw [hlaw j]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 1 ≤ (j:ℝ) / a := by rw [le_div_iff₀ ha]; linarith
      nlinarith [hp0 j]
    · have : {ω | N ω s - N ω 0 = j ∧ a < j} = ∅ := by
        ext ω; simp [hj]
      rw [this, measure_empty]; exact bot_le
  have hsum : HasSum (fun j : ℕ => (j:ℝ) / a * p j) (s / a) := by
    have e : (fun j : ℕ => (j:ℝ) / a * p j) =
        fun j : ℕ => (j:ℝ) * (Real.exp (-r) * (r:ℝ) ^ j / (j.factorial)) / a := by
      funext j; simp only [p]; ring
    rw [e, ← hrs]
    exact (mht62_hasSum_mean r).div_const a
  calc P {ω | a < N ω s} ≤ P (⋃ j : ℕ, {ω | N ω s - N ω 0 = j ∧ a < j}) := measure_mono hset
    _ ≤ ∑' j : ℕ, P {ω | N ω s - N ω 0 = j ∧ a < j} := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (j / a * p j) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (s / a) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by have := hp0 j; positivity)
          hsum.summable, hsum.tsum_eq]

/-- A single real random variable is tight. -/
lemma mht62_single {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℕ, μ {x | (R:ℝ) < |f x|} < ENNReal.ofReal δ := by
  set s : ℕ → Set α := fun k => {x | (k:ℝ) < |f x|}
  have hs : ∀ k, NullMeasurableSet (s k) μ := fun k =>
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp hf)).nullMeasurableSet
  have hm : Antitone s := by
    intro k l hkl x hx
    have : (k:ℝ) ≤ l := by exact_mod_cast hkl
    exact lt_of_le_of_lt this hx
  have hI : (⋂ k, s k) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := exists_nat_gt |f x|
    exact ⟨k, fun h => lt_irrefl _ (lt_trans h hk)⟩
  have ht := tendsto_measure_iInter_atTop hs hm ⟨0, measure_ne_top μ _⟩
  rw [hI, measure_empty] at ht
  obtain ⟨k, hk⟩ := ((tendsto_order.1 ht).2 _ (ENNReal.ofReal_pos.2 hδ)).exists
  exact ⟨k, hk⟩

/-- Convergence in distribution (with bounded continuous test functions) implies tightness. -/
lemma mht62_tight {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, 1 ≤ n → Measurable (Z n)) (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (Z n ω) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ))))
    (δ : ℝ) (hδ : 0 < δ) : ∃ R : ℝ, ∀ n, 1 ≤ n → P {ω | R < |Z n ω|} ≤ ENNReal.ofReal δ := by
  obtain ⟨R0, hR0⟩ := mht62_single (ν : Measure ℝ) id measurable_id (δ / 2) (by positivity)
  set g0 : ℝ → ℝ := fun x => min 1 (max 0 (|x| - R0))
  have hg0c : Continuous g0 := by fun_prop
  have hg0b : ∀ x, ‖g0 x‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have : 0 ≤ g0 x := le_min zero_le_one (le_max_left _ _)
      linarith
    · exact min_le_left _ _
  set g : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g0 hg0c 1 hg0b
  have hg : ∀ x, g x = g0 x := fun x => rfl
  -- upper bound by an indicator
  have hgν : ∫ x, g x ∂(ν : Measure ℝ) < δ / 2 := by
    have hmeas : MeasurableSet {x : ℝ | (R0:ℝ) < |id x|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp measurable_id)
    have h1 : ∫ x, g x ∂(ν : Measure ℝ) ≤
        ∫ x, ({x : ℝ | (R0:ℝ) < |id x|}.indicator 1 x) ∂(ν : Measure ℝ) := by
      refine integral_mono (g.integrable _) ((integrable_const 1).indicator hmeas) fun x => ?_
      rw [hg]
      by_cases hx : (R0:ℝ) < |x|
      · rw [Set.indicator_of_mem (by simpa using hx)]; exact min_le_left _ _
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        simp only [g0]
        rw [max_eq_left (by linarith [not_lt.1 hx])]
        exact min_le_right _ _
    rw [integral_indicator_one hmeas] at h1
    exact lt_of_le_of_lt h1 (ENNReal.toReal_lt_of_lt_ofReal hR0)
  have hev : ∀ᶠ n in atTop, ∫ ω, g (Z n ω) ∂P < δ / 2 :=
    (tendsto_order.1 (h0 g)).2 _ hgν
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hlarge : ∀ n, N ≤ n → 1 ≤ n → P {ω | (R0:ℝ) + 1 < |Z n ω|} ≤ ENNReal.ofReal δ := by
    intro n hn hn1
    have hmeas : MeasurableSet {ω | (R0:ℝ) + 1 < |Z n ω|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hZ n hn1))
    have hgi : Integrable (fun ω => g (Z n ω)) P :=
      Integrable.of_bound (g.continuous.measurable.comp (hZ n hn1)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by rw [hg]; exact hg0b _)
    have h1 : ∫ ω, ({ω | (R0:ℝ) + 1 < |Z n ω|}.indicator 1 ω) ∂P ≤ ∫ ω, g (Z n ω) ∂P := by
      refine integral_mono ((integrable_const 1).indicator hmeas) hgi fun ω => ?_
      simp only
      rw [hg]
      by_cases hx : (R0:ℝ) + 1 < |Z n ω|
      · rw [Set.indicator_of_mem (by simpa using hx)]
        simp only [g0, Pi.one_apply]
        rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        exact le_min zero_le_one (le_max_left _ _)
    rw [integral_indicator_one hmeas] at h1
    have h2 : P.real {ω | (R0:ℝ) + 1 < |Z n ω|} ≤ δ := by linarith [hN n hn]
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal h2
  have hsmall : ∀ n, ∃ R : ℝ, 1 ≤ n → P {ω | R < |Z n ω|} ≤ ENNReal.ofReal δ := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨R, hR⟩ := mht62_single P (Z n) (hZ n hn) δ hδ
      exact ⟨R, fun _ => hR.le⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose Rn hRn using hsmall
  refine ⟨(R0:ℝ) + 1 + ∑ m ∈ Finset.range N, |Rn m|, fun n hn => ?_⟩
  have hS : 0 ≤ ∑ m ∈ Finset.range N, |Rn m| := Finset.sum_nonneg fun m _ => abs_nonneg _
  rcases lt_or_ge n N with hnN | hnN
  · refine le_trans (measure_mono ?_) (hRn n hn)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h1 : Rn n ≤ |Rn n| := le_abs_self _
    have h2 : |Rn n| ≤ ∑ m ∈ Finset.range N, |Rn m| :=
      Finset.single_le_sum (f := fun m => |Rn m|) (fun m _ => abs_nonneg _)
        (Finset.mem_range.2 hnN)
    have h3 : (0:ℝ) ≤ (R0:ℝ) + 1 := by positivity
    linarith
  · refine le_trans (measure_mono ?_) (hlarge n hnN hn)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    linarith

theorem mht62_sb (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ))))
 :
    ∀ t : ℝ, 0 < t → IsSBReal P (fun n ω => phiS n μ (Q n) ω t) := by
  intro t ht ε hε
  haveI : IsProbabilityMeasure P := (hsys 1 le_rfl).isProb
  set Z : ℕ → Ω → ℝ := fun n ω => scaled n (Q n) ω 0 0 with hZdef
  have hZm : ∀ n, 1 ≤ n → Measurable (Z n) := by
    intro n hn
    have hq : Measurable (fun ω => (Q n ω 0 : ℝ)) :=
      (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp ((hsys n hn).meas 0)
    exact (hq.sub_const _).div_const _
  obtain ⟨R, hR⟩ := mht62_tight P Z hZm ν h0 (ε / 2) (by positivity)
  set a : ℝ := 2 * μ * t / ε with ha
  have hapos : 0 < a := by positivity
  refine ⟨μ * t * (R + 1 + a), fun n hn => ?_⟩
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hsysn := hsys n hn
  set bad : Set Ω := {ω | ¬ ∀ t : ℝ, 0 ≤ t →
      (Q n ω t : ℝ) = (Q n ω 0 : ℝ) + A n ω (n * μ * t) -
        S n ω (μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ))}
  have hbad : P bad = 0 := by
    have := hsysn.eqn
    rw [ae_iff] at this; exact this
  have hsubset : {ω | μ * t * (R + 1 + a) < |phiS n μ (Q n) ω t|} ⊆
      ({ω | R < |Z n ω|} ∪ {ω | n * a < A n ω (n * μ * t)}) ∪ bad := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_not, bad] at hcon
    obtain ⟨⟨hZ, hA⟩, hrep⟩ := hcon
    have h33 := MartingaleHT.InfiniteServer.lemma_3_3 (n * μ) μ (by positivity) hμ (A n ω)
      (S n ω) (Q n ω) (hsysn.poisson_A.mono ω)
      (fun u hu => by
        obtain ⟨m, hm⟩ := hsysn.poisson_S.nat_valued ω u hu
        rw [hm]; exact Nat.cast_nonneg _)
      (fun t ht => hsysn.integrable ω t ht) hrep t ht.le
    have hI0 : 0 ≤ ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ) :=
      intervalIntegral.integral_nonneg ht.le fun s _ => Nat.cast_nonneg _
    have hphi : |phiS n μ (Q n) ω t| = μ / n * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ) := by
      simp only [phiS]
      exact abs_of_nonneg (mul_nonneg (div_nonneg hμ.le hnpos.le) hI0)
    -- bound on Q(0)/n
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hsq1 : 1 ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]; exact_mod_cast hn
    have hZeq : (Q n ω 0 : ℝ) / n = 1 + Z n ω / Real.sqrt n := by
      simp only [Z, scaled]
      rw [div_div, hsq]
      field_simp
      ring
    have hZb : Z n ω / Real.sqrt n ≤ R := by
      have h1 : Z n ω / Real.sqrt n ≤ |Z n ω / Real.sqrt n| := le_abs_self _
      have h2 : |Z n ω / Real.sqrt n| ≤ |Z n ω| := by
        rw [abs_div, abs_of_pos hsqpos]
        exact div_le_self (abs_nonneg _) hsq1
      linarith
    have hAb : A n ω (n * μ * t) / n ≤ a := by
      rw [div_le_iff₀ hnpos]; linarith
    have hmain : μ / n * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ) ≤ μ * t * (R + 1 + a) := by
      have h1 : μ / n * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ) ≤
          μ / n * (t * ((Q n ω 0 : ℝ) + A n ω (n * μ * t))) :=
        mul_le_mul_of_nonneg_left h33.2 (div_nonneg hμ.le hnpos.le)
      have h2 : μ / n * (t * ((Q n ω 0 : ℝ) + A n ω (n * μ * t))) =
          μ * t * ((Q n ω 0 : ℝ) / n + A n ω (n * μ * t) / n) := by
        field_simp
      rw [h2, hZeq] at h1
      have h3 : μ * t * (1 + Z n ω / Real.sqrt n + A n ω (n * μ * t) / n) ≤
          μ * t * (R + 1 + a) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have : μ * t * (R + 1 + a) < |phiS n μ (Q n) ω t| := hω
    rw [hphi] at this
    linarith
  have hpois := mht62_poisson_tail P (A n) hsysn.poisson_A (n * μ * t) (by positivity) (n * a)
    (by positivity)
  have hratio : (n:ℝ) * μ * t / (n * a) = ε / 2 := by
    rw [ha]; field_simp
  rw [hratio] at hpois
  calc P {ω | μ * t * (R + 1 + a) < |phiS n μ (Q n) ω t|}
      ≤ P (({ω | R < |Z n ω|} ∪ {ω | n * a < A n ω (n * μ * t)}) ∪ bad) := measure_mono hsubset
    _ ≤ P {ω | R < |Z n ω|} + P {ω | n * a < A n ω (n * μ * t)} + P bad :=
        le_trans (measure_union_le _ _) (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) + 0 := by
        rw [hbad]
        exact add_le_add (add_le_add (hR n hn) hpois) le_rfl
    _ = ENNReal.ofReal ε := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- A Skorokhod path is bounded on every compact interval `[0, T]`. -/
lemma mht41_cadlag_bdd (x : ℝ → ℝ) (hx : IsCadlag x) (T : ℝ) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc (0:ℝ) T, |x s| ≤ B := by
  have key := (isCompact_Icc (a := (0:ℝ)) (b := T)).induction_on
    (p := fun s : Set ℝ => ∃ B : ℝ, ∀ y ∈ s, |x y| ≤ B)
    ⟨0, fun y hy => absurd hy (Set.notMem_empty y)⟩
    (fun s t hst ⟨B, hB⟩ => ⟨B, fun y hy => hB y (hst hy)⟩)
    (fun s t ⟨B₁, h₁⟩ ⟨B₂, h₂⟩ => ⟨max B₁ B₂, fun y hy => hy.elim
      (fun h => le_trans (h₁ y h) (le_max_left _ _))
      (fun h => le_trans (h₂ y h) (le_max_right _ _))⟩)
    ?_
  · exact key
  intro y hy
  have hy0 : 0 ≤ y := hy.1
  -- right neighbourhood
  have hR : {s | |x s| ≤ |x y| + 1} ∈ 𝓝[≥] y := by
    have hc := hx.1 y hy0
    have : ∀ᶠ s in 𝓝[≥] y, dist (x s) (x y) < 1 :=
      (Metric.tendsto_nhds.1 hc) 1 one_pos
    filter_upwards [this] with s hs
    rw [Real.dist_eq] at hs
    have := abs_sub_abs_le_abs_sub (x s) (x y)
    show |x s| ≤ |x y| + 1; linarith
  rcases eq_or_lt_of_le hy0 with h0 | hpos
  · subst h0
    refine ⟨{s | |x s| ≤ |x 0| + 1}, ?_, ⟨|x 0| + 1, fun s hs => hs⟩⟩
    exact nhdsWithin_mono _ (fun s hs => hs.1) hR
  · obtain ⟨l, hl⟩ := hx.2 y hpos
    have hL : {s | |x s| ≤ |l| + 1} ∈ 𝓝[<] y := by
      have : ∀ᶠ s in 𝓝[<] y, dist (x s) l < 1 := (Metric.tendsto_nhds.1 hl) 1 one_pos
      filter_upwards [this] with s hs
      rw [Real.dist_eq] at hs
      have := abs_sub_abs_le_abs_sub (x s) l
      show |x s| ≤ |l| + 1; linarith
    refine ⟨{s | |x s| ≤ |x y| + 1} ∪ {s | |x s| ≤ |l| + 1}, ?_, ?_⟩
    · apply mem_nhdsWithin_of_mem_nhds
      rw [← nhdsLT_sup_nhdsGE]
      exact ⟨Filter.mem_of_superset hL Set.subset_union_right,
        Filter.mem_of_superset hR Set.subset_union_left⟩
    · refine ⟨max (|x y| + 1) (|l| + 1), fun s hs => hs.elim
        (fun h => le_trans h (le_max_left _ _)) (fun h => le_trans h (le_max_right _ _))⟩

/-- A path that is right-continuous on `[0, ∞)`, frozen at its value at `0` on `(-∞, 0)`, is
Borel measurable. -/
lemma mht41_cadlag_meas (x : ℝ → ℝ) (hx : IsCadlag x) :
    Measurable (fun t => x (max t 0)) := by
  let f : ℕ → ℝ → ℝ := fun n t => x (max ((⌈((n:ℝ)+1) * t⌉ : ℝ) / ((n:ℝ)+1)) 0)
  have hf : ∀ n, Measurable (f n) := by
    intro n
    have h1 : Measurable (fun t : ℝ => ⌈((n:ℝ)+1) * t⌉) :=
      (measurable_const.mul measurable_id).ceil
    have h2 : Measurable (fun k : ℤ => x (max ((k : ℝ) / ((n:ℝ)+1)) 0)) :=
      measurable_from_top
    exact h2.comp h1
  refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 fun t => ?_)
  rcases lt_or_ge t 0 with ht | ht
  · have : ∀ n, f n t = x (max t 0) := by
      intro n
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have hc : ⌈((n:ℝ)+1) * t⌉ ≤ 0 := by
        rw [Int.ceil_le]; push_cast; nlinarith
      have : ((⌈((n:ℝ)+1) * t⌉ : ℤ) : ℝ) / ((n:ℝ)+1) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hc) hn.le
      simp only [f, max_eq_right this, max_eq_right ht.le]
    simp only [this]; exact tendsto_const_nhds
  · set u : ℕ → ℝ := fun n => (⌈((n:ℝ)+1) * t⌉ : ℝ) / ((n:ℝ)+1)
    have hu_ge : ∀ n, t ≤ u n := by
      intro n
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      rw [le_div_iff₀ hn, mul_comm]; exact Int.le_ceil _
    have hu_le : ∀ n, u n ≤ t + 1 / ((n:ℝ)+1) := by
      intro n
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have := Int.ceil_lt_add_one (((n:ℝ)+1) * t)
      have e : (t + 1 / ((n:ℝ)+1)) * ((n:ℝ)+1) = ((n:ℝ)+1) * t + 1 := by
        field_simp
      rw [div_le_iff₀ hn, e]
      linarith
    have hu : Tendsto u atTop (𝓝[≥] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hu_ge⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hu_ge hu_le
      have : Tendsto (fun n : ℕ => t + 1 / ((n:ℝ)+1)) atTop (𝓝 (t + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this
    have hcont := (hx.1 t ht).tendsto.comp hu
    have : ∀ n, f n t = x (u n) := by
      intro n; simp only [f, u]; rw [max_eq_left (le_trans ht (hu_ge n))]
    simp only [this, max_eq_left ht]
    exact hcont

lemma mht41_intOn (f : ℝ → ℝ) (hf : Measurable f) (T B : ℝ)
    (hB : ∀ s ∈ Set.Icc (0:ℝ) T, |f s| ≤ B) : IntegrableOn f (Set.Icc 0 T) := by
  refine Measure.integrableOn_of_bounded (M := B) (by simp) hf.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun s hs => by simpa [Real.norm_eq_abs] using hB s hs

/-- Frozen path bound: `x(max s 0)` is bounded on every half-line `(-∞, T]`. -/
lemma mht41_frozen_bdd (x : ℝ → ℝ) (hx : IsCadlag x) (T : ℝ) :
    ∃ B : ℝ, ∀ s, s ≤ T → |x (max s 0)| ≤ B := by
  obtain ⟨B, hB⟩ := mht41_cadlag_bdd x hx (max T 0)
  exact ⟨B, fun s hs => hB _ ⟨le_max_right _ _, max_le_max_right 0 hs⟩⟩

lemma mht41_intg (h : ℝ → ℝ) (c : ℝ) (hhc : Continuous h)
    (hhx : ∀ s, |h s| ≤ |h 0| + c * |s|) (hc : 0 ≤ c)
    (F : ℝ → ℝ) (hFm : Measurable F) (hFb : ∀ T, ∃ B : ℝ, ∀ s, s ≤ T → |F s| ≤ B)
    (w : ℝ → ℝ) (a b : ℝ) (hw : ContinuousOn w (Set.uIcc a b)) :
    IntervalIntegrable (fun s => h (F s + w s)) volume a b := by
  rw [intervalIntegrable_iff]
  obtain ⟨Cw, hCw⟩ := isCompact_uIcc.exists_bound_of_continuousOn hw
  obtain ⟨B, hB⟩ := hFb (max a b)
  have hsub : Set.uIoc a b ⊆ Set.uIcc a b := Set.uIoc_subset_uIcc
  show Integrable _ (volume.restrict (Set.uIoc a b))
  rw [← integrableOn_univ]
  refine Measure.integrableOn_of_bounded (M := |h 0| + c * (B + Cw)) ?_ ?_ ?_
  · rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Set.uIoc]; simp
  · exact (hhc.comp_aestronglyMeasurable
      (hFm.aestronglyMeasurable.add (hw.aestronglyMeasurable measurableSet_uIcc))).mono_set hsub
  · rw [Measure.restrict_univ]
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hs' := hsub hs
    have h1 : |F s| ≤ B := hB s (Set.mem_uIcc.1 hs' |>.elim (fun h => le_trans h.2 (le_max_right _ _))
      (fun h => le_trans h.2 (le_max_left _ _)))
    have h2 : |w s| ≤ Cw := by simpa [Real.norm_eq_abs] using hCw s hs'
    rw [Real.norm_eq_abs]
    refine le_trans (hhx _) ?_
    have := abs_add_le (F s) (w s)
    nlinarith

/-- Comparison lemma (Gronwall), used for uniqueness and continuity of the solution map. -/
lemma mht41_cmp (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|)
    (x₁ x₂ : ℝ → ℝ) (h₁ : IsCadlag x₁) (h₂ : IsCadlag x₂) (T ε : ℝ) (hε : 0 < ε)
    (e : ℝ → ℝ) (he : ∀ t ∈ Set.Icc (0:ℝ) T, |e t| ≤ ε)
    (heq : ∀ t ∈ Set.Icc (0:ℝ) T, x₁ t - x₂ t =
      e t + ((∫ s in (0:ℝ)..t, h (x₁ s)) - ∫ s in (0:ℝ)..t, h (x₂ s))) :
    ∀ t ∈ Set.Icc (0:ℝ) T, |x₁ t - x₂ t| ≤ ε * Real.exp (c * T) := by
  have hhc : Continuous h := by
    have : LipschitzWith ⟨c, hc.le⟩ h := LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.dist_eq, Real.dist_eq]; exact hLip a b
    exact this.continuous
  set F₁ : ℝ → ℝ := fun t => x₁ (max t 0)
  set F₂ : ℝ → ℝ := fun t => x₂ (max t 0)
  have hF₁ : Measurable F₁ := mht41_cadlag_meas x₁ h₁
  have hF₂ : Measurable F₂ := mht41_cadlag_meas x₂ h₂
  obtain ⟨B₁, hB₁⟩ := mht41_cadlag_bdd x₁ h₁ T
  obtain ⟨B₂, hB₂⟩ := mht41_cadlag_bdd x₂ h₂ T
  have hhx : ∀ s, |h s| ≤ |h 0| + c * |s| := by
    intro s
    have := hLip s 0
    simp only [sub_zero] at this
    have := abs_sub_abs_le_abs_sub (h s) (h 0)
    linarith
  set g : ℝ → ℝ := fun s => |F₁ s - F₂ s|
  have hgm : Measurable g := continuous_abs.measurable.comp (hF₁.sub hF₂)
  have hgi : IntegrableOn g (Set.Icc 0 T) := by
    refine mht41_intOn g hgm T (B₁ + B₂) fun s hs => ?_
    simp only [g, F₁, F₂, max_eq_left hs.1, abs_abs]
    have := abs_sub (x₁ s) (x₂ s)
    linarith [hB₁ s hs, hB₂ s hs]
  have hi₁ : IntegrableOn (fun s => h (F₁ s)) (Set.Icc 0 T) :=
    mht41_intOn _ (hhc.measurable.comp hF₁) T (|h 0| + c * B₁) fun s hs => by
      refine le_trans (hhx _) ?_
      have := hB₁ s hs
      simp only [F₁, max_eq_left hs.1]; nlinarith
  have hi₂ : IntegrableOn (fun s => h (F₂ s)) (Set.Icc 0 T) :=
    mht41_intOn _ (hhc.measurable.comp hF₂) T (|h 0| + c * B₂) fun s hs => by
      refine le_trans (hhx _) ?_
      have := hB₂ s hs
      simp only [F₂, max_eq_left hs.1]; nlinarith
  have hG := MartingaleHT.InfiniteServer.lemma_4_1 g T ε c hε hc hgm hgi ?_
  · intro t ht
    have := hG t ht
    simp only [g, F₁, F₂, max_eq_left ht.1] at this
    refine le_trans this (mul_le_mul_of_nonneg_left ?_ hε.le)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hc.le)
  intro t ht
  refine ⟨abs_nonneg _, ?_⟩
  have ht0 : 0 ≤ t := ht.1
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hgt : g t = |x₁ t - x₂ t| := by simp [g, F₁, F₂, max_eq_left ht0]
  have hc1 : ∫ s in (0:ℝ)..t, h (x₁ s) = ∫ s in (0:ℝ)..t, h (F₁ s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht0] at hs
    simp [F₁, max_eq_left hs.1]
  have hc2 : ∫ s in (0:ℝ)..t, h (x₂ s) = ∫ s in (0:ℝ)..t, h (F₂ s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht0] at hs
    simp [F₂, max_eq_left hs.1]
  have hI₁ : IntervalIntegrable (fun s => h (F₁ s)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hi₁.mono_set hsub
  have hI₂ : IntervalIntegrable (fun s => h (F₂ s)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hi₂.mono_set hsub
  have hIg : IntervalIntegrable g volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hgi.mono_set hsub
  have hint : |(∫ s in (0:ℝ)..t, h (F₁ s)) - ∫ s in (0:ℝ)..t, h (F₂ s)|
      ≤ c * ∫ s in (0:ℝ)..t, g s := by
    rw [← intervalIntegral.integral_sub hI₁ hI₂]
    calc |∫ s in (0:ℝ)..t, (h (F₁ s) - h (F₂ s))|
        ≤ ∫ s in (0:ℝ)..t, |h (F₁ s) - h (F₂ s)| := by
          have := intervalIntegral.norm_integral_le_integral_norm
            (f := fun s => h (F₁ s) - h (F₂ s)) (μ := volume) ht0
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∫ s in (0:ℝ)..t, c * g s :=
          intervalIntegral.integral_mono_on ht0 (hI₁.sub hI₂).abs (hIg.const_mul c)
            fun s _ => hLip _ _
      _ = c * ∫ s in (0:ℝ)..t, g s := intervalIntegral.integral_const_mul _ _
  rw [hgt, heq t ht, hc1, hc2]
  have := abs_add_le (e t) ((∫ s in (0:ℝ)..t, h (F₁ s)) - ∫ s in (0:ℝ)..t, h (F₂ s))
  linarith [he t ht]


/-- Second factorial moment of the Poisson law: `∑ j (j-1) e^{-r} r^j / j! = r²`. -/
lemma mht43_hasSum_fact2 (r : ℝ≥0) :
    HasSum (fun j : ℕ => ((j : ℝ) * ((j : ℝ) - 1)) * (Real.exp (-r) * (r:ℝ) ^ j / (j.factorial)))
      ((r:ℝ) ^ 2) := by
  have H := (hasSum_one_poissonMeasure r).mul_left ((r:ℝ) ^ 2)
  rw [mul_one] at H
  have e : ∀ n : ℕ, (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) *
      (Real.exp (-r) * (r:ℝ) ^ (n + 2) / ((n + 2).factorial))
      = (r:ℝ) ^ 2 * (Real.exp (-r) * (r:ℝ) ^ n / (n.factorial)) := by
    intro n
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have H2 : HasSum (fun n : ℕ => (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) *
      (Real.exp (-r) * (r:ℝ) ^ (n + 2) / ((n + 2).factorial)))
      ((r:ℝ) ^ 2 - ∑ i ∈ Finset.range 2, ((i : ℝ) * ((i : ℝ) - 1)) *
        (Real.exp (-r) * (r:ℝ) ^ i / (i.factorial))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      zero_mul, sub_self, mul_zero, zero_add, sub_zero]
    simp only [e]
    exact H
  exact (hasSum_nat_add_iff' 2).1 H2

/-- Variance of the Poisson law: `∑ (j - r)² e^{-r} r^j / j! = r`. -/
lemma mht43_hasSum_var (r : ℝ≥0) :
    HasSum (fun j : ℕ => ((j : ℝ) - r) ^ 2 * (Real.exp (-r) * (r:ℝ) ^ j / (j.factorial))) r := by
  have h1 := mht43_hasSum_fact2 r
  have h2 := mht62_hasSum_mean r
  have h3 := hasSum_one_poissonMeasure r
  have := ((h1.add h2).sub (h2.mul_left (2 * (r:ℝ)))).add (h3.mul_left ((r:ℝ) ^ 2))
  have e1 : (fun j : ℕ => ((j : ℝ) - r) ^ 2 * (Real.exp (-r) * (r:ℝ) ^ j / (j.factorial))) =
      fun b : ℕ => ((b:ℝ) * ((b:ℝ) - 1) * (Real.exp (-r) * (r:ℝ) ^ b / (b.factorial)) +
        (b:ℝ) * (Real.exp (-r) * (r:ℝ) ^ b / (b.factorial)) -
        2 * (r:ℝ) * ((b:ℝ) * (Real.exp (-r) * (r:ℝ) ^ b / (b.factorial)))) +
        (r:ℝ) ^ 2 * (Real.exp (-r) * (r:ℝ) ^ b / (b.factorial)) := by
    funext j; ring
  have e2 : (r:ℝ) ^ 2 + r - 2 * r * r + (r:ℝ) ^ 2 * 1 = r := by ring
  rw [e2] at this
  rw [e1]
  exact this

/-- Chebyshev bound for a rate-one Poisson process: `P(|N(s) − s| > a) ≤ s / a²`. -/
lemma mht43_cheb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → ℝ → ℝ)
    (hN : IsPoissonProcess P N 1) (s : ℝ) (hs : 0 ≤ s) (a : ℝ) (ha : 0 < a) :
    P {ω | a < |N ω s - s|} ≤ ENNReal.ofReal (s / a ^ 2) := by
  set r : ℝ≥0 := (1 * (s - 0)).toNNReal with hr
  have hrs : (r : ℝ) = s := by rw [hr]; simp [hs]
  set p : ℕ → ℝ := fun j => Real.exp (-r) * (r:ℝ) ^ j / (j.factorial)
  have hp0 : ∀ j, 0 ≤ p j := fun j => by positivity
  have hlaw : ∀ j : ℕ, P {ω | N ω s - N ω 0 = j} = ENNReal.ofReal (p j) := by
    intro j
    rw [hN.law 0 s le_rfl hs j, poissonMeasure_singleton]
  have hset : {ω | a < |N ω s - s|} ⊆ ⋃ j : ℕ, {ω | N ω s - N ω 0 = j ∧ a < |(j:ℝ) - s|} := by
    intro ω hω
    obtain ⟨m, hm⟩ := hN.nat_valued ω s hs
    refine Set.mem_iUnion.2 ⟨m, ?_, ?_⟩
    · simp [hN.zero ω, hm]
    · have : a < |N ω s - s| := hω
      rwa [hm] at this
  have hterm : ∀ j : ℕ, P {ω | N ω s - N ω 0 = j ∧ a < |(j:ℝ) - s|} ≤
      ENNReal.ofReal (((j:ℝ) - s) ^ 2 / a ^ 2 * p j) := by
    intro j
    by_cases hj : a < |(j:ℝ) - s|
    · have hsub : {ω | N ω s - N ω 0 = j ∧ a < |(j:ℝ) - s|} ⊆ {ω | N ω s - N ω 0 = j} :=
        fun ω hω => hω.1
      refine le_trans (measure_mono hsub) ?_
      rw [hlaw j]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 1 ≤ ((j:ℝ) - s) ^ 2 / a ^ 2 := by
        rw [le_div_iff₀ (by positivity), one_mul, ← sq_abs ((j:ℝ) - s)]
        exact pow_le_pow_left₀ ha.le hj.le 2
      nlinarith [hp0 j]
    · have : {ω | N ω s - N ω 0 = j ∧ a < |(j:ℝ) - s|} = ∅ := by
        ext ω; simp [hj]
      rw [this, measure_empty]; exact bot_le
  have hsum : HasSum (fun j : ℕ => ((j:ℝ) - s) ^ 2 / a ^ 2 * p j) (s / a ^ 2) := by
    have e : (fun j : ℕ => ((j:ℝ) - s) ^ 2 / a ^ 2 * p j) =
        fun j : ℕ => ((j:ℝ) - r) ^ 2 * (Real.exp (-r) * (r:ℝ) ^ j / (j.factorial)) / a ^ 2 := by
      funext j; simp only [p]; rw [hrs]; ring
    rw [e, ← hrs]
    exact (mht43_hasSum_var r).div_const _
  calc P {ω | a < |N ω s - s|}
      ≤ P (⋃ j : ℕ, {ω | N ω s - N ω 0 = j ∧ a < |(j:ℝ) - s|}) := measure_mono hset
    _ ≤ ∑' j : ℕ, P {ω | N ω s - N ω 0 = j ∧ a < |(j:ℝ) - s|} := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (((j:ℝ) - s) ^ 2 / a ^ 2 * p j) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (s / a ^ 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by have := hp0 j; positivity)
          hsum.summable, hsum.tsum_eq]

/-- Functional weak law of large numbers for a rate-one Poisson process, with an explicit
rate: `P(sup_{0 ≤ u ≤ C} |N(nu) − nu| > ηn) ≤ K/n`. -/
lemma mht43_fwlln {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → ℝ → ℝ)
    (hN : IsPoissonProcess P N 1) (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) (n : ℕ) (hn : 1 ≤ n) :
    P {ω | ∃ u ∈ Set.Icc (0:ℝ) C, η * n < |N ω (n * u) - n * u|} ≤
      ENNReal.ofReal (((⌈2 * C / η⌉₊ + 2 : ℕ) : ℝ) * (4 * C / η ^ 2) / n) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · subst hC0
    have : {ω | ∃ u ∈ Set.Icc (0:ℝ) 0, η * n < |N ω (n * u) - n * u|} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_lt]
      intro u hu
      have : u = 0 := le_antisymm hu.2 hu.1
      subst this
      simp [hN.zero ω]; positivity
    rw [this, measure_empty]; exact bot_le
  set k : ℕ := ⌈2 * C / η⌉₊ + 1 with hk
  have hkpos : (0:ℝ) < k := by positivity
  have hCk : C / k ≤ η / 2 := by
    have h1 : 2 * C / η < k := by
      rw [hk]; push_cast; linarith [Nat.le_ceil (2 * C / η)]
    rw [div_lt_iff₀ hη] at h1
    rw [div_le_iff₀ hkpos]; nlinarith
  set g : ℕ → ℝ := fun i => i * C / k
  have hg0 : ∀ i, 0 ≤ g i := fun i => by positivity
  have hgC : ∀ i ∈ Finset.range (k + 1), g i ≤ C := by
    intro i hi
    have : (i:ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    simp only [g]; rw [div_le_iff₀ hkpos]; nlinarith
  have hset : {ω | ∃ u ∈ Set.Icc (0:ℝ) C, η * n < |N ω (n * u) - n * u|} ⊆
      ⋃ i ∈ Finset.range (k + 1), {ω | η * n / 2 < |N ω (n * g i) - n * g i|} := by
    intro ω hω
    obtain ⟨u, hu, hlt⟩ := hω
    set x : ℝ := u * k / C
    have hx0 : 0 ≤ x := by have := hu.1; positivity
    have hxk : x ≤ k := by
      simp only [x]; rw [div_le_iff₀ hCpos]; nlinarith [hu.2]
    set i := ⌊x⌋₊
    set j := ⌈x⌉₊
    have hi : i ∈ Finset.range (k + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.floor_le_of_le hxk))
    have hj : j ∈ Finset.range (k + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.ceil_le.2 hxk))
    have hgi : g i ≤ u := by
      have : (i:ℝ) ≤ x := Nat.floor_le hx0
      simp only [g, x] at this ⊢
      rw [div_le_iff₀ hkpos]
      rw [le_div_iff₀ hCpos] at this
      nlinarith
    have hgj : u ≤ g j := by
      have : x ≤ (j:ℝ) := Nat.le_ceil x
      simp only [g, x] at this ⊢
      rw [le_div_iff₀ hkpos]
      rw [div_le_iff₀ hCpos] at this
      nlinarith
    have hji : g j - g i ≤ η / 2 := by
      have : (j:ℝ) ≤ i + 1 := by exact_mod_cast Nat.ceil_le_floor_add_one x
      have : g j - g i ≤ C / k := by
        simp only [g]; rw [← sub_div, div_le_div_iff_of_pos_right hkpos]; nlinarith
      linarith
    have hmono := hN.mono ω
    have hNi : N ω (n * g i) ≤ N ω (n * u) :=
      hmono (by show 0 ≤ (n:ℝ) * g i; have := hg0 i; positivity)
        (by show 0 ≤ (n:ℝ) * u; have := hu.1; positivity)
        (mul_le_mul_of_nonneg_left hgi hnpos.le)
    have hNj : N ω (n * u) ≤ N ω (n * g j) :=
      hmono (by show 0 ≤ (n:ℝ) * u; have := hu.1; positivity)
        (by show 0 ≤ (n:ℝ) * g j; have := hg0 j; positivity)
        (mul_le_mul_of_nonneg_left hgj hnpos.le)
    have hd1 : (n:ℝ) * (g j - u) ≤ n * (η / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hnpos.le
    have hd2 : (n:ℝ) * (u - g i) ≤ n * (η / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hnpos.le
    rcases lt_abs.1 hlt with hpos | hneg
    · refine Set.mem_biUnion hj ?_
      show η * n / 2 < |N ω (n * g j) - n * g j|
      refine lt_of_lt_of_le ?_ (le_abs_self _)
      nlinarith
    · refine Set.mem_biUnion hi ?_
      show η * n / 2 < |N ω (n * g i) - n * g i|
      refine lt_of_lt_of_le ?_ (neg_le_abs _)
      nlinarith
  calc P {ω | ∃ u ∈ Set.Icc (0:ℝ) C, η * n < |N ω (n * u) - n * u|}
      ≤ P (⋃ i ∈ Finset.range (k + 1), {ω | η * n / 2 < |N ω (n * g i) - n * g i|}) :=
        measure_mono hset
    _ ≤ ∑ i ∈ Finset.range (k + 1), P {ω | η * n / 2 < |N ω (n * g i) - n * g i|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (4 * C / η ^ 2 / n) := by
        refine Finset.sum_le_sum fun i hi => le_trans
          (mht43_cheb P N hN (n * g i) (by have := hg0 i; positivity) (η * n / 2)
            (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
        rw [div_le_div_iff₀ (by positivity) hnpos]
        have := hgC i hi
        have h2 : (η * n / 2) ^ 2 = η ^ 2 * n ^ 2 / 4 := by ring
        rw [h2]
        have : (n:ℝ) * g i * n ≤ 4 * C / η ^ 2 * (η ^ 2 * n ^ 2 / 4) := by
          have e : 4 * C / η ^ 2 * (η ^ 2 * n ^ 2 / 4) = C * n ^ 2 := by
            field_simp
          rw [e]; nlinarith [hg0 i]
        linarith
    _ = ENNReal.ofReal (((⌈2 * C / η⌉₊ + 2 : ℕ) : ℝ) * (4 * C / η ^ 2) / n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hk]; push_cast; ring

lemma mht43_cadlag_affine (f : ℝ → ℝ) (hf : IsCadlag f) (a b : ℝ) :
    IsCadlag (fun t => f t / a - b) :=
  ⟨fun t ht => ((hf.1 t ht).div_const a).sub_const b,
   fun t ht => by
    obtain ⟨l, hl⟩ := hf.2 t ht
    exact ⟨l / a - b, (hl.div_const a).sub_const b⟩⟩

theorem solution (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) :
    UocInProb P (fun n ω t (_ : Fin 1) => psiS n (Q n) ω t) (fun _ _ => 1) := by
  intro T hT ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  set δr : ℝ := (min δ 1).toReal with hδr
  have hmin_ne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hδr_pos : 0 < δr := by
    rw [hδr]; exact ENNReal.toReal_pos (by simp [hδ.ne']) hmin_ne
  have hδr_le : ENNReal.ofReal δr ≤ δ := by
    rw [hδr, ENNReal.ofReal_toReal hmin_ne]; exact min_le_left _ _
  haveI : IsProbabilityMeasure P := (hsys 1 le_rfl).isProb
  set E : ℝ := Real.exp (μ * T) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set η : ℝ := ε / (4 * E) with hη
  have hηpos : 0 < η := by positivity
  set Z : ℕ → Ω → ℝ := fun n ω => scaled n (Q n) ω 0 0 with hZdef
  have hZm : ∀ n, 1 ≤ n → Measurable (Z n) := by
    intro n hn
    have hq : Measurable (fun ω => (Q n ω 0 : ℝ)) :=
      (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp ((hsys n hn).meas 0)
    exact (hq.sub_const _).div_const _
  obtain ⟨R, hR⟩ := mht62_tight P Z hZm ν h0 (δr / 4) (by positivity)
  obtain ⟨C, hC⟩ := mht62_sb μ hμ P A S Q hsys ν h0 (T + 1) (by linarith) (δr / 4)
    (by positivity)
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hμT : 0 ≤ μ * T := by positivity
  set KA : ℝ := ((⌈2 * (μ * T) / η⌉₊ + 2 : ℕ) : ℝ) * (4 * (μ * T) / η ^ 2) with hKA
  set KS : ℝ := ((⌈2 * C' / η⌉₊ + 2 : ℕ) : ℝ) * (4 * C' / η ^ 2) with hKS
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ (R / η) ^ 2 ≤ n ∧ 4 * KA / δr ≤ n ∧
      4 * KS / δr ≤ n :=
    (eventually_ge_atTop 1).and ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
        (tendsto_natCast_atTop_atTop.eventually_ge_atTop _)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn1, hnR, hnA, hnS⟩ := hN n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsysn := hsys n hn1
  set bad : Set Ω := {ω | ¬ ∀ t : ℝ, 0 ≤ t →
      (Q n ω t : ℝ) = (Q n ω 0 : ℝ) + A n ω (n * μ * t) -
        S n ω (μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ))} with hbaddef
  have hbad : P bad = 0 := by
    have := hsysn.eqn
    rw [ae_iff] at this; exact this
  set E0 : Set Ω := {ω | R < |Z n ω|} with hE0
  set E1 : Set Ω := {ω | C < |phiS n μ (Q n) ω (T + 1)|} with hE1
  set E2 : Set Ω := {ω | ∃ u ∈ Set.Icc (0:ℝ) (μ * T), η * n < |A n ω (n * u) - n * u|}
    with hE2
  set E3 : Set Ω := {ω | ∃ u ∈ Set.Icc (0:ℝ) C', η * n < |S n ω (n * u) - n * u|} with hE3
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsubset : {ω | ENNReal.ofReal ε ≤
      supDist (fun t (_ : Fin 1) => psiS n (Q n) ω t) (fun _ _ => 1) T} ⊆
      E0 ∪ E1 ∪ E2 ∪ E3 ∪ bad := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨h0', h1'⟩, h2'⟩, h3'⟩, hgood⟩ := hcon
    simp only [hE0, hE1, hE2, hE3, hbaddef, Set.mem_setOf_eq, not_lt, not_exists, not_and,
      not_not] at h0' h1' h2' h3' hgood
    have hLip : ∀ s₁ s₂ : ℝ, |(fun x => -μ * x) s₁ - (fun x => -μ * x) s₂| ≤ μ * |s₁ - s₂| := by
      intro a b
      simp only
      rw [show -μ * a - -μ * b = -μ * (a - b) by ring, abs_mul, abs_neg, abs_of_pos hμ]
    have hx1 : IsCadlag (fun t => (Q n ω t : ℝ) / n - 1) :=
      mht43_cadlag_affine _ (hsysn.cadlag ω) n 1
    have hx2 : IsCadlag (fun _ : ℝ => (0:ℝ)) :=
      ⟨fun t _ => continuousWithinAt_const, fun t _ => ⟨0, tendsto_const_nhds⟩⟩
    set e : ℝ → ℝ := fun t => ((Q n ω 0 : ℝ) / n - 1) + (A n ω (n * μ * t) - n * μ * t) / n
      - (S n ω (μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ)) - μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ)) / n
      with hedef
    have he : ∀ t ∈ Set.Icc (0:ℝ) T, |e t| ≤ 3 * η := by
      intro t ht
      -- initial term
      have hZeq : (Q n ω 0 : ℝ) / n - 1 = Z n ω / Real.sqrt n := by
        simp only [Z, scaled]
        rw [div_div, hsq]
        field_simp
      have hb0 : |(Q n ω 0 : ℝ) / n - 1| ≤ η := by
        rw [hZeq, abs_div, abs_of_pos hsqpos, div_le_iff₀ hsqpos]
        have h1 : |R / η| ≤ Real.sqrt n := Real.abs_le_sqrt hnR
        have h2 : R / η ≤ Real.sqrt n := le_trans (le_abs_self _) h1
        rw [div_le_iff₀ hηpos] at h2
        linarith [h0']
      -- arrival term
      have hb1 : |(A n ω (n * μ * t) - n * μ * t) / n| ≤ η := by
        have := h2' (μ * t) ⟨by have := ht.1; positivity,
          mul_le_mul_of_nonneg_left ht.2 hμ.le⟩
        rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
        have e1 : (n:ℝ) * μ * t = n * (μ * t) := by ring
        rw [e1]; linarith
      -- service term
      have hI0 : 0 ≤ ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ) :=
        intervalIntegral.integral_nonneg ht.1 fun s _ => Nat.cast_nonneg _
      have hmonoI : ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ) ≤ ∫ s in (0 : ℝ)..(T + 1), (Q n ω s : ℝ) :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 (by linarith [ht.2])
          (ae_of_all _ fun s => Nat.cast_nonneg _) (hsysn.integrable ω (T + 1) (by linarith))
      have hb2 : |(S n ω (μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ)) -
          μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ)) / n| ≤ η := by
        set u : ℝ := μ / n * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ) with hu
        have hnu : (n:ℝ) * u = μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ) := by
          rw [hu]; field_simp
        have hu0 : 0 ≤ u := by positivity
        have huC : u ≤ C' := by
          have h1 : u ≤ phiS n μ (Q n) ω (T + 1) := by
            simp only [phiS, hu]
            exact mul_le_mul_of_nonneg_left hmonoI (by positivity)
          have h2 : phiS n μ (Q n) ω (T + 1) ≤ C := le_trans (le_abs_self _) h1'
          linarith [le_max_left C 0]
        have := h3' u ⟨hu0, huC⟩
        rw [hnu] at this
        rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
        linarith
      simp only [hedef]
      have := abs_sub (((Q n ω 0 : ℝ) / n - 1) + (A n ω (n * μ * t) - n * μ * t) / n)
        ((S n ω (μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ)) -
          μ * ∫ s in (0 : ℝ)..t, (Q n ω s : ℝ)) / n)
      have := abs_add_le ((Q n ω 0 : ℝ) / n - 1) ((A n ω (n * μ * t) - n * μ * t) / n)
      linarith
    have heq : ∀ t ∈ Set.Icc (0:ℝ) T, ((Q n ω t : ℝ) / n - 1) - 0 =
        e t + ((∫ s in (0:ℝ)..t, (fun x => -μ * x) ((Q n ω s : ℝ) / n - 1)) -
          ∫ s in (0:ℝ)..t, (fun x => -μ * x) ((fun _ : ℝ => (0:ℝ)) s)) := by
      intro t ht
      have hI : IntervalIntegrable (fun s => (Q n ω s : ℝ)) volume 0 t :=
        hsysn.integrable ω t ht.1
      have hint : ∫ s in (0:ℝ)..t, (fun x => -μ * x) ((Q n ω s : ℝ) / n - 1) =
          -μ * ((∫ s in (0:ℝ)..t, (Q n ω s : ℝ)) / n - t) := by
        simp only
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub (hI.div_const _) intervalIntegrable_const,
          intervalIntegral.integral_div]
        simp
      rw [hint]
      simp only [mul_zero, intervalIntegral.integral_zero, sub_zero, hedef]
      rw [hgood t ht.1]
      field_simp
      ring
    have hkey := mht41_cmp (fun x => -μ * x) μ hμ hLip _ _ hx1 hx2 T (3 * η) (by positivity)
      e he heq
    have hle : supDist (fun t (_ : Fin 1) => psiS n (Q n) ω t) (fun _ _ => 1) T ≤
        ENNReal.ofReal (3 * η * E) := by
      unfold supDist
      refine iSup₂_le fun s hs => ENNReal.ofReal_le_ofReal ?_
      have := hkey s hs
      simpa [psiS] using this
    have hlt : ENNReal.ofReal (3 * η * E) < ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_lt_ofReal_iff hε]
      have : 3 * η * E = 3 * ε / 4 := by rw [hη]; field_simp
      rw [this]; linarith
    have hω' : ENNReal.ofReal ε ≤
        supDist (fun t (_ : Fin 1) => psiS n (Q n) ω t) (fun _ _ => 1) T := hω
    exact absurd hω' (not_le.2 (lt_of_le_of_lt hle hlt))
  have hA := mht43_fwlln P (A n) hsysn.poisson_A (μ * T) η hμT hηpos n hn1
  have hS := mht43_fwlln P (S n) hsysn.poisson_S C' η hC'0 hηpos n hn1
  have hKAn : KA / n ≤ δr / 4 := by
    rw [div_le_iff₀ hnpos]
    rw [div_le_iff₀ hδr_pos] at hnA
    linarith
  have hKSn : KS / n ≤ δr / 4 := by
    rw [div_le_iff₀ hnpos]
    rw [div_le_iff₀ hδr_pos] at hnS
    linarith
  calc P {ω | ENNReal.ofReal ε ≤
        supDist (fun t (_ : Fin 1) => psiS n (Q n) ω t) (fun _ _ => 1) T}
      ≤ P (E0 ∪ E1 ∪ E2 ∪ E3 ∪ bad) := measure_mono hsubset
    _ ≤ P E0 + P E1 + P E2 + P E3 + P bad := by
        refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
        refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
        refine le_trans (measure_union_le _ _) (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (δr / 4) + ENNReal.ofReal (δr / 4) + ENNReal.ofReal (δr / 4) +
          ENNReal.ofReal (δr / 4) + 0 := by
        rw [hbad]
        refine add_le_add (add_le_add (add_le_add (add_le_add (hR n hn1) (hC n hn1))
          (le_trans hA (ENNReal.ofReal_le_ofReal hKAn)))
          (le_trans hS (ENNReal.ofReal_le_ofReal hKSn))) le_rfl
    _ = ENNReal.ofReal δr := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ δ := hδr_le
