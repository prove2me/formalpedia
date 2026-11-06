-- Prove2me | solution 1 for MartingaleHT.InfiniteServer.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:39:46.883208+00:00
-- url     : https://prove2.me/submissions/0aefe347-16db-4af5-a6db-688fa53ce7b3

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit
import Theorems.Thm_MartingaleHT_InfiniteServer_lemma_3_3

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

theorem solution (μ : ℝ) (hμ : 0 < μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A S : ℕ → Ω → ℝ → ℝ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsMMInfSystem P (n * μ) μ (A n) (S n) (Q n))
    (ν : ProbabilityMeasure ℝ)
    (h0 : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ ω, g (scaled n (Q n) ω 0 0) ∂P) atTop
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ))))
    (hmom : ∀ n : ℕ, 1 ≤ n → Integrable (fun ω => (Q n ω 0 : ℝ)) P) :
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
