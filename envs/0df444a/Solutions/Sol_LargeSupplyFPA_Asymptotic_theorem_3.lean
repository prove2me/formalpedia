-- Prove2me | solution 1 for LargeSupplyFPA.Asymptotic.theorem_3
-- status  : ACCEPTED   (disprove)
-- author  : @jasonhartline
-- created : 2026-11-14T15:40:51.225639+00:00
-- url     : https://prove2.me/submissions/5dafd349-e223-44bc-bc7f-77fc12557a1b

import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds

open MeasureTheory ProbabilityTheory Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

/-- Sum the utility comparison over an optimal set, while retaining all bidders'
nonnegative adjusted utilities. This charges the deviation loss at most k times. -/
theorem topK_comparison {n : ℕ} (k : ℕ) (v u : Fin n → ℝ) (B price error : ℝ)
    (hB : 0 ≤ B) (hprice : 0 ≤ price) (herror : 0 ≤ error)
    (hu0 : ∀ i, 0 ≤ u i)
    (hu : ∀ i, B * v i ≤ u i + price + error) :
    B * topKSum k v ≤ (∑ i, u i) + (k : ℝ) * (price + error) := by
  classical
  by_cases hb : B = 0
  · rw [hb, zero_mul]
    exact add_nonneg (Finset.sum_nonneg fun i _ => hu0 i)
      (mul_nonneg (by positivity) (add_nonneg hprice herror))
  have hbpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hb)
  rw [mul_comm B, ← le_div_iff₀ hbpos]
  unfold topKSum
  let : Nonempty {S : Finset (Fin n) // S.card ≤ k} := ⟨⟨∅, by simp⟩⟩
  apply ciSup_le
  intro S
  apply (le_div_iff₀ hbpos).2
  rw [mul_comm, Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ S.val, (u i + (price + error)) :=
      Finset.sum_le_sum fun i _ => by linarith [hu i]
    _ = (∑ i ∈ S.val, u i) + (S.val.card : ℝ) * (price + error) := by
      simp [Finset.sum_add_distrib, nsmul_eq_mul, mul_add]
    _ ≤ _ := add_le_add
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hu0 i))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast S.property) (add_nonneg hprice herror))

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

theorem marginalBid_probability {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (i : Fin n) :
    IsProbabilityMeasure (marginalBid V E i) := by
  let hv := hV i
  let he := (hE i).1
  exact isProbabilityMeasure_bind (E i).aemeasurable (Filter.Eventually.of_forall fun _ => inferInstance)

theorem marginalBid_negative_zero {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    (hE : IsStrategyProfile E) (i : Fin n) : marginalBid V E i (Set.Iio 0) = 0 := by
  rw [marginalBid, Measure.bind_apply measurableSet_Iio (E i).aemeasurable,
    lintegral_congr_ae (Filter.Eventually.of_forall ((hE i).2)), lintegral_zero]

private theorem continuous_cdf_of_atomless (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ b : ℝ, μ {b} = 0) : Continuous (ProbabilityTheory.cdf μ : ℝ → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro b
  let F := ProbabilityTheory.cdf μ
  apply F.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [F.rightLim_eq]
  have hz := F.measure_singleton b
  rw [show F.measure = μ from measure_cdf μ, h b] at hz
  have hleft := F.mono.leftLim_le (le_refl b)
  have hz' := ENNReal.ofReal_eq_zero.mp hz.symm
  linarith [show Function.leftLim (F : ℝ → ℝ) b ≤ F b from hleft]

theorem continuous_expNumAbove {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    [∀ i, IsProbabilityMeasure (marginalBid V E i)] (h : IsAtomless V E) :
    Continuous (expNumAbove V E) := by
  unfold expNumAbove
  apply continuous_finsetSum
  intro i _
  have heq (b : ℝ) : (marginalBid V E i).real (Set.Ioi b) =
      1 - ProbabilityTheory.cdf (marginalBid V E i) b := by
    rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]
  simp_rw [heq]
  exact continuous_const.sub (continuous_cdf_of_atomless _ (h i))

theorem tendsto_expNumAbove {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    [∀ i, IsProbabilityMeasure (marginalBid V E i)] :
    Tendsto (expNumAbove V E) atTop (𝓝 0) := by
  unfold expNumAbove
  have hsum (i : Fin n) : Tendsto (fun b : ℝ => (marginalBid V E i).real (Set.Ioi b))
      atTop (𝓝 0) := by
    have heq (b : ℝ) : (marginalBid V E i).real (Set.Ioi b) =
        1 - ProbabilityTheory.cdf (marginalBid V E i) b := by
      rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]
    simp_rw [heq]
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atTop (marginalBid V E i))
  simpa using tendsto_finsetSum Finset.univ (fun i _ => hsum i)

theorem antitone_expNumAbove {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    [∀ i, IsProbabilityMeasure (marginalBid V E i)] :
    Antitone (expNumAbove V E) := by
  intro a b hab
  exact Finset.sum_le_sum fun i _ => measureReal_mono (Set.Ioi_subset_Ioi hab)

theorem threshold_mem {f : ℝ → ℝ} (hc : Continuous f)
    (hf : Tendsto f atTop (𝓝 0)) {q : ℝ} (hq : 0 < q) :
    sInf {b : ℝ | 0 ≤ b ∧ f b ≤ q} ∈ {b : ℝ | 0 ≤ b ∧ f b ≤ q} := by
  have hclosed : IsClosed {b : ℝ | 0 ≤ b ∧ f b ≤ q} :=
    isClosed_Ici.inter (isClosed_le hc continuous_const)
  have hEventually : ∀ᶠ x : ℝ in atTop, 0 ≤ x ∧ f x ≤ q :=
    (eventually_ge_atTop 0).and (hf.eventually (eventually_le_nhds hq))
  obtain ⟨x, hx⟩ := hEventually.exists
  exact hclosed.csInf_mem ⟨x, hx⟩ ⟨0, fun _ hy => hy.1⟩

theorem highThreshold_upper_count (δ : ℝ) {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} [∀ i, IsProbabilityMeasure (marginalBid V E i)]
    (hA4 : IsAtomless V E) {b : ℝ} (hb : highThreshold δ k V E ≤ b)
    (hq : 0 < (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1) :
    expNumAbove V E b ≤ (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 := by
  have h := threshold_mem (continuous_expNumAbove hA4) (tendsto_expNumAbove (V := V) (E := E)) hq
  exact (antitone_expNumAbove hb).trans h.2

theorem lowThreshold_lower_count (δ : ℝ) {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} [∀ i, IsProbabilityMeasure (marginalBid V E i)]
    (hA4 : IsAtomless V E) {b : ℝ} (_hb : 0 ≤ b)
    (hb' : b ≤ lowThreshold δ k V E) (hpos : 0 < lowThreshold δ k V E) :
    (k : ℝ) + (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 ≤ expNumAbove V E b := by
  let q := (k : ℝ) + (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1
  let t := lowThreshold δ k V E
  suffices ht : q ≤ expNumAbove V E t from ht.trans (antitone_expNumAbove hb')
  by_contra! hlt
  have hOpen : IsOpen {x | 0 < x ∧ expNumAbove V E x < q} :=
    isOpen_Ioi.inter (isOpen_lt (continuous_expNumAbove hA4) continuous_const)
  have hmem : t ∈ {x | 0 < x ∧ expNumAbove V E x < q} := ⟨hpos, hlt⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hOpen t hmem
  have hball : t - ε / 2 ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have : t - ε / 2 - t = -(ε / 2) := by ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
    linarith
  have hx := hsub hball
  have hle : t ≤ t - ε / 2 := csInf_le ⟨0, fun _ hy => hy.1⟩ ⟨hx.1.le, hx.2.le⟩
  linarith

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

theorem max_subset {n : ℕ} (k : ℕ) (v : Fin n → ℝ) (hk : k ≤ n) :
    ∃ S : Finset (Fin n), S.card = k ∧
      ∀ T : Finset (Fin n), T.card = k → (∑ i ∈ T, v i) ≤ ∑ i ∈ S, v i := by
  classical
  let candidates := (Finset.univ : Finset (Finset (Fin n))).filter fun T => T.card = k
  have hn : candidates.Nonempty := by
    have hc : k ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hk
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq hc
    exact ⟨S, by simp [candidates, hS]⟩
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image (fun T => ∑ i ∈ T, v i) hn
  exact ⟨S, (Finset.mem_filter.mp hS).2, fun T hT => hmax T (by simp [candidates, hT])⟩

theorem fractional_le_topK {n : ℕ} (k : ℕ) (v a : Fin n → ℝ) (hk : k ≤ n)
    (hv : ∀ i, 0 ≤ v i) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hsum : (∑ i, a i) ≤ k) :
    (∑ i, v i * a i) ≤ topKSum k v := by
  classical
  obtain ⟨S, hS, hmax⟩ := max_subset k v hk
  have ht : (∑ i ∈ S, v i) ≤ topKSum k v := by
    unfold topKSum
    refine le_ciSup (f := fun T : {T : Finset (Fin n) // T.card ≤ k} =>
      ∑ i ∈ T.val, v i) ?_ ⟨S, hS.le⟩
    exact (Set.finite_range _).bddAbove
  apply le_trans _ ht
  by_cases hSempty : S.Nonempty
  · obtain ⟨j, hj, hjmin⟩ := S.exists_min_image v hSempty
    have hOut (i : Fin n) (hi : i ∉ S) : v i ≤ v j := by
      have hi' : i ∉ S.erase j := fun h => hi (Finset.mem_of_mem_erase h)
      have hc : (insert i (S.erase j)).card = k := by
        rw [Finset.card_insert_of_notMem hi', Finset.card_erase_of_mem hj, hS]
        have := Finset.card_pos.mpr hSempty
        omega
      have hswap := hmax (insert i (S.erase j)) hc
      rw [Finset.sum_insert hi'] at hswap
      have heq := S.sum_erase_add v hj
      linarith
    have hc : (∑ i ∈ S, (1 - a i)) =
        (k : ℝ) - ∑ i ∈ S, a i := by
      simp [Finset.sum_sub_distrib, hS]
    have hma : (∑ i ∈ Finset.univ \ S, a i) ≤ ∑ i ∈ S, (1 - a i) := by
      have heq := Finset.sum_sdiff (f := a) (Finset.subset_univ S)
      rw [hc]
      linarith
    have hleft : (∑ i ∈ Finset.univ \ S, v i * a i) ≤ v j * ∑ i ∈ Finset.univ \ S, a i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
        (hOut i (Finset.mem_sdiff.mp hi).2) (ha i).1
    have hright : v j * (∑ i ∈ S, (1 - a i)) ≤ ∑ i ∈ S, v i * (1 - a i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (hjmin i hi) (sub_nonneg.mpr (ha i).2)
    have hh := hleft.trans ((mul_le_mul_of_nonneg_left hma (hv j)).trans hright)
    have heq := Finset.sum_sdiff (f := fun i => v i * a i) (Finset.subset_univ S)
    have hsplit : (∑ i ∈ S, v i * (1 - a i)) =
        (∑ i ∈ S, v i) - ∑ i ∈ S, v i * a i := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    linarith
  · have hzero : k = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hSempty] at hS
      exact hS.symm
    have ha0 (i : Fin n) : a i = 0 := by
      have hle := Finset.single_le_sum (fun j _ => (ha j).1) (Finset.mem_univ i)
      rw [hzero, Nat.cast_zero] at hsum
      linarith [(ha i).1]
    simp [ha0, Finset.not_nonempty_iff_eq_empty.mp hSempty]

theorem measurable_topKSum {n : ℕ} (k : ℕ) : Measurable (topKSum (n := n) k) := by
  classical
  let : Nonempty {S : Finset (Fin n) // S.card ≤ k} := ⟨⟨∅, by simp⟩⟩
  unfold topKSum
  simp_rw [← Finset.sup'_univ_eq_ciSup]
  apply Continuous.measurable
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro S _
  exact continuous_finsetSum _ fun i _ => continuous_apply i

theorem topKSum_nonneg {n : ℕ} (k : ℕ) (v : Fin n → ℝ) : 0 ≤ topKSum k v := by
  unfold topKSum
  simpa using (le_ciSup (f := fun S : {S : Finset (Fin n) // S.card ≤ k} =>
    ∑ i ∈ S.val, v i) (Set.finite_range _).bddAbove ⟨∅, by simp⟩)

theorem topKSum_le {n : ℕ} (k : ℕ) (v : Fin n → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hv : ∀ i, v i ≤ H) : topKSum k v ≤ (k : ℝ) * H := by
  unfold topKSum
  let : Nonempty {S : Finset (Fin n) // S.card ≤ k} := ⟨⟨∅, by simp⟩⟩
  apply ciSup_le
  intro S
  calc
    _ ≤ ∑ _i ∈ S.val, H := Finset.sum_le_sum fun i _ => hv i
    _ = (S.val.card : ℝ) * H := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast S.property) hH

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} (B : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (B j)]

noncomputable def bidCount (s : Finset (Fin n)) (b : ℝ) (β : Fin n → ℝ) : ℝ :=
  ∑ j ∈ s, (Set.Ioi b).indicator (fun _ : ℝ => (1 : ℝ)) (β j)

noncomputable def bidCountMean (s : Finset (Fin n)) (b : ℝ) : ℝ :=
  ∑ j ∈ s, (B j).real (Set.Ioi b)

theorem bidCount_eq_card (s : Finset (Fin n)) (b : ℝ) (β : Fin n → ℝ) :
    bidCount s b β = ((s.filter fun j => b < β j).card : ℝ) := by
  classical
  simp [bidCount, Set.indicator]

private theorem indicator_memLp (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    MemLp ((Set.Ioi b).indicator (fun _ => (1 : ℝ))) 2 μ :=
  memLp_indicator_const 2 measurableSet_Ioi 1 (Or.inr (measure_ne_top _ _))

theorem measurable_bidCount (s : Finset (Fin n)) (b : ℝ) :
    Measurable (bidCount s b) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_const.indicator measurableSet_Ioi).comp (measurable_pi_apply j)

private theorem bidCount_memLp (s : Finset (Fin n)) (b : ℝ) :
    MemLp (bidCount s b) 2 (Measure.pi B) := by
  classical
  have h (j : Fin n) : MemLp (fun β : Fin n → ℝ =>
      (Set.Ioi b).indicator (fun _ => (1 : ℝ)) (β j)) 2 (Measure.pi B) :=
    (indicator_memLp (B j) b).comp_measurePreserving (measurePreserving_eval B j)
  unfold bidCount
  exact memLp_finsetSum s fun j _ => h j

theorem integral_bidCount (s : Finset (Fin n)) (b : ℝ) :
    (∫ β, bidCount s b β ∂Measure.pi B) = bidCountMean B s b := by
  have h (j : Fin n) : Integrable (fun β : Fin n → ℝ =>
      (Set.Ioi b).indicator (fun _ => (1 : ℝ)) (β j)) (Measure.pi B) :=
    ((indicator_memLp (B j) b).comp_measurePreserving
      (measurePreserving_eval B j)).integrable (by norm_num)
  unfold bidCount bidCountMean
  rw [integral_finsetSum _ fun j _ => h j]
  apply Finset.sum_congr rfl
  intro j _
  change (∫ a, (Set.Ioi b).indicator (1 : ℝ → ℝ) (Function.eval j a)
    ∂Measure.pi B) = _
  let f := (Set.Ioi b).indicator (1 : ℝ → ℝ)
  have hmap : (Measure.pi B).map (Function.eval j) = B j :=
    (measurePreserving_eval B j).map_eq
  have hf : AEStronglyMeasurable f ((Measure.pi B).map (Function.eval j)) :=
    ((measurable_const (a := (1 : ℝ))).indicator measurableSet_Ioi).aestronglyMeasurable
  calc
    (∫ a, f (Function.eval j a) ∂Measure.pi B) =
      ∫ x, f x ∂(Measure.pi B).map (Function.eval j) :=
        (integral_map (measurable_pi_apply j).aemeasurable hf).symm
    _ = (B j).real (Set.Ioi b) := by
      rw [hmap]
      exact integral_indicator_one measurableSet_Ioi

private theorem variance_bidCount_le_mean (s : Finset (Fin n)) (b : ℝ) :
    variance (bidCount s b) (Measure.pi B) ≤ bidCountMean B s b := by
  classical
  let X : Fin n → ℝ → ℝ := fun j =>
    if j ∈ s then (Set.Ioi b).indicator (fun _ => 1) else 0
  have hlp (j : Fin n) : MemLp (X j) 2 (B j) := by
    by_cases hj : j ∈ s
    · simpa [X, hj] using indicator_memLp (B j) b
    · simp [X, hj]
  have hsum : bidCount s b = ∑ j : Fin n, fun β : Fin n → ℝ => X j (β j) := by
    funext β
    simp only [bidCount, X, Finset.sum_apply, ite_apply, Pi.zero_apply]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hsum, variance_sum_pi hlp]
  unfold bidCountMean
  have h (j : Fin n) : variance (X j) (B j) ≤
      if j ∈ s then (B j).real (Set.Ioi b) else 0 := by
    by_cases hj : j ∈ s
    · simp only [X, hj, if_true]
      refine (variance_le_expectation_sq (indicator_memLp (B j) b).1).trans_eq ?_
      have heq : ((Set.Ioi b).indicator (fun _ : ℝ => (1 : ℝ))) ^ 2 =
          (Set.Ioi b).indicator (fun _ => 1) := by
        funext x
        by_cases hx : x ∈ Set.Ioi b <;> simp [Set.indicator, hx]
      rw [heq]
      exact integral_indicator_one measurableSet_Ioi
    · simp [X, hj]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  simpa [← Finset.sum_filter] using hsum

theorem bidCount_deviation (s : Finset (Fin n)) (b : ℝ) {r : ℝ} (hr : 0 < r) :
    (Measure.pi B).real {β | r ≤ |bidCount s b β - bidCountMean B s b|} ≤
      bidCountMean B s b / r ^ 2 := by
  have h := meas_ge_le_variance_div_sq (bidCount_memLp B s b) hr
  rw [integral_bidCount B s b] at h
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))]
  exact div_le_div_of_nonneg_right (variance_bidCount_le_mean B s b) (sq_nonneg _)

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

theorem eventually_threshold_scale (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5) :
    ∀ᶠ k : ℕ in atTop,
      4 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ) ∧ (k : ℝ) ^ ((0.5 : ℝ) + δ) ≤ k ∧
      0 < (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 := by
  have hExp : 0 < (0.5 : ℝ) + δ := by linarith [hδ.1]
  have hGap : 0 < 1 - ((0.5 : ℝ) + δ) := by linarith [hδ.2]
  have hlarge := (tendsto_rpow_atTop hExp).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := (tendsto_rpow_neg_atTop hGap).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlarge.eventually (eventually_ge_atTop (4 : ℝ)),
    hsmall.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_ge_atTop (4 : ℕ)] with k hlarge hsmall hk
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hkP : 0 < (k : ℝ) := by linarith
  change 4 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ) at hlarge
  change (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) < 1 / 2 at hsmall
  have hrewrite : (k : ℝ) ^ ((0.5 : ℝ) + δ) =
      (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) * (k : ℝ) := by
    conv_rhs => rw [← Real.rpow_add_one hkP.ne']
    congr 1
    ring
  have hhalf : (k : ℝ) ^ ((0.5 : ℝ) + δ) < (k : ℝ) / 2 := by
    rw [hrewrite]
    linarith [mul_lt_mul_of_pos_right hsmall hkP]
  exact ⟨hlarge, by linarith, by linarith⟩

theorem tendsto_tail_error (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => 8 * (k : ℝ) / ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (8 : ℝ))).mul
    ((tendsto_rpow_neg_atTop (show 0 < 2 * δ by positivity)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hp : 0 < (k : ℝ) := by exact_mod_cast hk
  change 8 * (k : ℝ) ^ (-(2 * δ)) = 8 * (k : ℝ) / ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2
  have hden : ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2 = (k : ℝ) ^ (1 + 2 * δ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hp.le]
    congr 1
    push_cast
    ring
  have hratio : (k : ℝ) / (k : ℝ) ^ (1 + 2 * δ) = (k : ℝ) ^ (-(2 * δ)) := by
    calc
      _ = (k : ℝ) ^ (1 : ℝ) / (k : ℝ) ^ (1 + 2 * δ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hp]; congr 1 <;> ring
  rw [hden, mul_div_assoc, hratio]

private theorem lowerTailRatio {k t m : ℝ} (ht : 4 ≤ t) (htk : t ≤ k)
    (hm : k + t - 2 ≤ m) : m / (m - k) ^ 2 ≤ 8 * k / t ^ 2 := by
  have hk : 0 < k := by linarith
  have ht0 : 0 < t := by linarith
  have hg : 0 < m - k := by linarith
  have hm0 : 0 < m := by linarith
  by_cases hmk : m ≤ 2 * k
  · have hsq : t ^ 2 ≤ 4 * (m - k) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 2 * (m - k) - t by linarith)
        (show 0 ≤ 2 * (m - k) + t by linarith)]
    apply (div_le_div_iff₀ (sq_pos_of_pos hg) (sq_pos_of_pos ht0)).2
    calc
      m * t ^ 2 ≤ (2 * k) * t ^ 2 :=
        mul_le_mul_of_nonneg_right hmk (sq_nonneg _)
      _ ≤ (2 * k) * (4 * (m - k) ^ 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (8 * k) * (m - k) ^ 2 := by ring
  · have hratio : m / (m - k) ^ 2 ≤ 4 / m := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hg) hm0).2
      nlinarith [mul_nonneg (show 0 ≤ 2 * (m - k) - m by linarith)
        (show 0 ≤ 2 * (m - k) + m by linarith)]
    refine hratio.trans ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hk
      (by linarith)).trans ?_)
    apply (div_le_div_iff₀ hk (sq_pos_of_pos ht0)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr htk) (show 0 ≤ k + t by linarith)]

theorem lower_tail_bound {n : ℕ} (B : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (B j)]
    (s : Finset (Fin n)) (b : ℝ) (k : ℕ) {t : ℝ} (ht : 4 ≤ t) (htk : t ≤ k)
    (hm : (k : ℝ) + t - 2 ≤ bidCountMean B s b) :
    (Measure.pi B).real {β | bidCount s b β < k} ≤ 8 * k / t ^ 2 := by
  have hg : 0 < bidCountMean B s b - k := by linarith
  refine (measureReal_mono (μ := Measure.pi B) (s₂ := {β |
    bidCountMean B s b - k ≤ |bidCount s b β - bidCountMean B s b|}) ?_).trans ?_
  · intro β hβ
    change bidCount s b β < k at hβ
    exact (show bidCountMean B s b - k ≤ -(bidCount s b β - bidCountMean B s b) by
      linarith).trans (neg_le_abs _)
  exact (bidCount_deviation B s b hg).trans (lowerTailRatio ht htk hm)

theorem upper_tail_bound {n : ℕ} (B : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (B j)]
    (s : Finset (Fin n)) (b : ℝ) (k : ℕ) {t : ℝ} (ht : 4 ≤ t)
    (hm : bidCountMean B s b ≤ (k : ℝ) - t - 1) :
    (Measure.pi B).real {β | (k : ℝ) ≤ bidCount s b β} ≤ 8 * k / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  refine (measureReal_mono (μ := Measure.pi B)
    (s₂ := {β | t ≤ |bidCount s b β - bidCountMean B s b|}) ?_).trans ?_
  · intro β hβ
    change (k : ℝ) ≤ bidCount s b β at hβ
    exact (show t ≤ bidCount s b β - bidCountMean B s b by linarith).trans (le_abs_self _)
  have hk : 0 ≤ (k : ℝ) := by positivity
  exact (bidCount_deviation B s b ht0).trans
    (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable [∀ j, IsProbabilityMeasure (marginalBid V E j)]

omit [∀ j, IsProbabilityMeasure (marginalBid V E j)] in
theorem kthBidCDF_eq_count (k : ℕ) (b : ℝ) :
    kthBidCDF k V E b =
      (Measure.pi (marginalBid V E)).real {β | bidCount Finset.univ b β < k} := by
  unfold kthBidCDF
  congr 1
  ext β
  simp only [mem_ofPred_eq, bidCount_eq_card, numAbove, Nat.cast_lt]

private theorem bidCount_zero_ae (hE : IsStrategyProfile E) (hA4 : IsAtomless V E)
    (s : Finset (Fin n)) :
    ∀ᵐ β ∂Measure.pi (marginalBid V E), bidCount s 0 β = s.card := by
  have hCoord (j : Fin n) :
      ∀ᵐ β ∂Measure.pi (marginalBid V E), 0 < β j := by
    have hz : marginalBid V E j (Set.Iic 0) = 0 := by
      have hu : Set.Iio (0 : ℝ) ∪ {0} = Set.Iic 0 := by
        ext x
        simp [le_iff_lt_or_eq]
      rw [← hu, measure_union_null (marginalBid_negative_zero (V := V) hE j) (hA4 j 0)]
    rw [ae_iff]
    simpa only [not_lt, Set.preimage, Function.eval, Set.mem_Iic] using
      Measure.pi_eval_preimage_null (marginalBid V E) hz
  filter_upwards [ae_all_iff.mpr hCoord] with β hβ
  rw [bidCount_eq_card]
  rw [Finset.filter_eq_self.mpr (fun j _ => hβ j)]

private theorem bidCountMean_erase_lower (i : Fin n) (b : ℝ) :
    expNumAbove V E b - 1 ≤ bidCountMean (marginalBid V E) (Finset.univ.erase i) b := by
  have h := Finset.sum_erase_add (s := Finset.univ)
    (fun j => (marginalBid V E j).real (Set.Ioi b)) (Finset.mem_univ i)
  unfold expNumAbove bidCountMean
  linarith [show (marginalBid V E i).real (Set.Ioi b) ≤ 1 from measureReal_le_one]

theorem low_bid_tail (δ : ℝ) (k : ℕ) (hE : IsStrategyProfile E)
    (hA4 : IsAtomless V E) (s : Finset (Fin n)) (hs : k ≤ s.card) (b : ℝ)
    (hb : 0 ≤ b ∧ b ≤ lowThreshold δ k V E)
    (hmean : expNumAbove V E b - 1 ≤ bidCountMean (marginalBid V E) s b)
    (hScale : 4 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ))
    (hScaleK : (k : ℝ) ^ ((0.5 : ℝ) + δ) ≤ k) :
    (Measure.pi (marginalBid V E)).real {β | bidCount s b β < k} ≤
      8 * k / ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2 := by
  rcases lt_or_ge 0 (lowThreshold δ k V E) with hpos | hzero
  · have hc := lowThreshold_lower_count δ k hA4 hb.1 hb.2 hpos
    exact lower_tail_bound (marginalBid V E) s b k hScale hScaleK (by linarith)
  · have hb0 : b = 0 := le_antisymm (hb.2.trans hzero) hb.1
    subst b
    have hz : (Measure.pi (marginalBid V E)).real {β | bidCount s 0 β < k} = 0 := by
      have hh : ({β | bidCount s 0 β < k} : Set (Fin n → ℝ))
          =ᵐ[Measure.pi (marginalBid V E)] (∅ : Set (Fin n → ℝ)) := by
        filter_upwards [bidCount_zero_ae hE hA4 s] with β hβ
        change (bidCount s 0 β < (k : ℝ)) = False
        rw [hβ]
        exact eq_false (not_lt_of_ge (by exact_mod_cast hs))
      rw [measureReal_congr hh, measureReal_empty]
    rw [hz]
    positivity

theorem kthBidCDF_low_bound (δ : ℝ) (k : ℕ) (hkn : k < n) (hE : IsStrategyProfile E)
    (hA4 : IsAtomless V E) (b : ℝ) (hb : 0 ≤ b ∧ b ≤ lowThreshold δ k V E)
    (hScale : 4 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ))
    (hScaleK : (k : ℝ) ^ ((0.5 : ℝ) + δ) ≤ k) :
    kthBidCDF k V E b ≤ 8 * k / ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2 := by
  rw [kthBidCDF_eq_count]
  apply low_bid_tail δ k hE hA4 Finset.univ (by simpa using hkn.le) b hb _ hScale hScaleK
  change expNumAbove V E b - 1 ≤ expNumAbove V E b
  linarith

theorem kthBidCDF_high_bound (δ : ℝ) (k : ℕ) (hA4 : IsAtomless V E)
    (b : ℝ) (hb : highThreshold δ k V E ≤ b)
    (hScale : 4 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ))
    (hHigh : 0 < (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1) :
    1 - kthBidCDF k V E b ≤ 8 * k / ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2 := by
  rw [kthBidCDF_eq_count, ← probReal_compl_eq_one_sub
    (measurableSet_lt (measurable_bidCount Finset.univ b) measurable_const)]
  simp only [Set.compl_ofPred, not_lt]
  exact upper_tail_bound (marginalBid V E) Finset.univ b k hScale
    (highThreshold_upper_count δ k hA4 hb hHigh)

omit [∀ j, IsProbabilityMeasure (marginalBid V E j)] in
theorem alloc_nonneg (k : ℕ) (i : Fin n) (b : ℝ) : 0 ≤ alloc k V E i b := by
  apply integral_nonneg
  intro β
  unfold tieShare
  exact le_min (div_nonneg (le_max_right _ _) (by positivity)) zero_le_one

theorem alloc_le_one (k : ℕ) (i : Fin n) (b : ℝ) : alloc k V E i b ≤ 1 := by
  change (∫ β, tieShare k i b β ∂Measure.pi (marginalBid V E)) ≤ 1
  calc
    _ ≤ ∫ _ : Fin n → ℝ, (1 : ℝ) ∂Measure.pi (marginalBid V E) := by
      apply integral_mono_of_nonneg _ (integrable_const _) _
      · exact Filter.Eventually.of_forall fun β =>
          le_min (div_nonneg (le_max_right _ _) (by positivity)) zero_le_one
      · exact Filter.Eventually.of_forall fun _ => min_le_right _ _
    _ = 1 := by simp

theorem alloc_le_tail (k : ℕ) (i : Fin n) (b : ℝ) :
    alloc k V E i b ≤ (Measure.pi (marginalBid V E)).real
      {β | bidCount (Finset.univ.erase i) b β < k} := by
  classical
  let event : Set (Fin n → ℝ) := {β | bidCount (Finset.univ.erase i) b β < k}
  have hevent : MeasurableSet event :=
    measurableSet_lt (measurable_bidCount (Finset.univ.erase i) b) measurable_const
  change (∫ β, tieShare k i b β ∂Measure.pi (marginalBid V E)) ≤
    (Measure.pi (marginalBid V E)).real event
  rw [← integral_indicator_one hevent]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun β =>
      le_min (div_nonneg (le_max_right _ _) (by positivity)) zero_le_one
  · exact (integrable_const (1 : ℝ)).indicator hevent
  · apply Filter.Eventually.of_forall
    intro β
    by_cases h : β ∈ event
    · rw [Set.indicator_of_mem h]
      change tieShare k i b β ≤ (1 : ℝ)
      exact min_le_right _ _
    · have hcard : (k : ℝ) ≤ ((Finset.univ.filter fun j => j ≠ i ∧ b < β j).card : ℝ) := by
        have hh : (k : ℝ) ≤ bidCount (Finset.univ.erase i) b β := le_of_not_gt h
        rw [bidCount_eq_card] at hh
        have hfilter : (Finset.univ.erase i).filter (fun j => b < β j) =
            Finset.univ.filter (fun j => j ≠ i ∧ b < β j) := by
          ext j
          simp
        rwa [hfilter] at hh
      simp [Set.indicator_of_notMem h, tieShare, max_eq_right (sub_nonpos.mpr hcard)]

theorem alloc_low_bound (δ : ℝ) (k : ℕ) (hkn : k < n) (hE : IsStrategyProfile E)
    (hA4 : IsAtomless V E) (i : Fin n) (b : ℝ) (hb : 0 ≤ b ∧ b ≤ lowThreshold δ k V E)
    (hScale : 4 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ))
    (hScaleK : (k : ℝ) ^ ((0.5 : ℝ) + δ) ≤ k) :
    alloc k V E i b ≤ 8 * k / ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2 := by
  apply (alloc_le_tail k i b).trans
  apply low_bid_tail δ k hE hA4 (Finset.univ.erase i) _ b hb
    (bidCountMean_erase_lower i b) hScale hScaleK
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

theorem cutoff_exists {n : ℕ} (k : ℕ) (β : Fin n → ℝ) (hk0 : 0 < k) (hkn : k ≤ n) :
    ∃ p : ℝ, (Finset.univ.filter fun i => p < β i).card < k ∧
      k ≤ (Finset.univ.filter fun i => p ≤ β i).card := by
  classical
  obtain ⟨S, hS, hmax⟩ := max_subset k β hkn
  have hnonempty : S.Nonempty := Finset.card_pos.mp (hS.symm ▸ hk0)
  obtain ⟨j, hj, hjmin⟩ := S.exists_min_image β hnonempty
  have hOut (i : Fin n) (hi : i ∉ S) : β i ≤ β j := by
    have hi' : i ∉ S.erase j := fun h => hi (Finset.mem_of_mem_erase h)
    have hc : (insert i (S.erase j)).card = k := by
      rw [Finset.card_insert_of_notMem hi', Finset.card_erase_of_mem hj, hS]
      omega
    have hswap := hmax (insert i (S.erase j)) hc
    rw [Finset.sum_insert hi'] at hswap
    linarith [S.sum_erase_add β hj]
  refine ⟨β j, ?_, ?_⟩
  · have hsub : Finset.univ.filter (fun i => β j < β i) ⊆ S.erase j := by
      intro i hi
      have hgt := (Finset.mem_filter.mp hi).2
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro hij
        subst i
        exact (lt_irrefl _) hgt
      · by_contra hm
        exact (not_lt_of_ge (hOut i hm)) hgt
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hj, hS] at hc
    omega
  · rw [← hS]
    exact Finset.card_le_card (fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hjmin i hi⟩)

theorem tieShare_nonneg {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) (β : Fin n → ℝ) :
    0 ≤ tieShare k i b β := by
  unfold tieShare
  exact le_min (div_nonneg (le_max_right _ _) (by positivity)) zero_le_one

theorem tieShare_le_one {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) (β : Fin n → ℝ) :
    tieShare k i b β ≤ 1 := min_le_right _ _

private theorem count_split {n : ℕ} (β : Fin n → ℝ) (p : ℝ) :
    (Finset.univ.filter fun i => p ≤ β i).card =
      (Finset.univ.filter fun i => p < β i).card +
      (Finset.univ.filter fun i => β i = p).card := by
  classical
  let a := Finset.univ.filter fun i : Fin n => p < β i
  let b := Finset.univ.filter fun i : Fin n => β i = p
  have hD : Disjoint a b := by
    rw [Finset.disjoint_left]
    intro i ha hb
    exact (ne_of_gt (Finset.mem_filter.mp ha).2) (Finset.mem_filter.mp hb).2
  have hU : a ∪ b = Finset.univ.filter fun i => p ≤ β i := by
    ext i
    simp [a, b, le_iff_lt_or_eq, eq_comm (a := p)]
  rw [← hU, Finset.card_union_of_disjoint hD]

theorem tieShare_formula {n : ℕ} (k : ℕ) (β : Fin n → ℝ) (p : ℝ)
    (hlo : (Finset.univ.filter fun i => p < β i).card < k)
    (hhi : k ≤ (Finset.univ.filter fun i => p ≤ β i).card) (i : Fin n) :
    tieShare k i (β i) β = if p < β i then 1 else if β i = p then
      ((k : ℝ) - ((Finset.univ.filter fun j => p < β j).card : ℝ)) /
        ((Finset.univ.filter fun j => β j = p).card : ℝ) else 0 := by
  classical
  let A := Finset.univ.filter fun j : Fin n => p < β j
  let T := Finset.univ.filter fun j : Fin n => β j = p
  have hsplit := count_split β p
  by_cases hi : p < β i
  · rw [if_pos hi]
    apply min_eq_right
    have hSub : (Finset.univ.filter fun j => j ≠ i ∧ β i < β j) ∪
        (Finset.univ.filter fun j => j ≠ i ∧ β j = β i) ⊆ A.erase i := by
      intro j hj
      rcases Finset.mem_union.mp hj with h | h
      · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hi.trans (Finset.mem_filter.mp h).2.2⟩⟩
      · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp h).2.2.symm ▸ hi⟩⟩
    have hD : Disjoint (Finset.univ.filter fun j => j ≠ i ∧ β i < β j)
        (Finset.univ.filter fun j => j ≠ i ∧ β j = β i) := by
      rw [Finset.disjoint_left]
      intro j ha ht
      exact (ne_of_gt (Finset.mem_filter.mp ha).2.2) (Finset.mem_filter.mp ht).2.2
    have hcard := Finset.card_le_card hSub
    rw [Finset.card_union_of_disjoint hD,
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩ : i ∈ A)] at hcard
    have hNat : 1 + (Finset.univ.filter fun j => j ≠ i ∧ β j = β i).card +
        (Finset.univ.filter fun j => j ≠ i ∧ β i < β j).card ≤ k := by
      have hApos : 0 < (Finset.univ.filter fun j => p < β j).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
      omega
    have hReal : 1 + ((Finset.univ.filter fun j => j ≠ i ∧ β j = β i).card : ℝ) +
        ((Finset.univ.filter fun j => j ≠ i ∧ β i < β j).card : ℝ) ≤ k := by
      exact_mod_cast hNat
    rw [le_div_iff₀ (by positivity), one_mul]
    exact (show _ ≤ (k : ℝ) - ((Finset.univ.filter fun j => j ≠ i ∧ β i < β j).card : ℝ)
      by linarith).trans (le_max_left _ _)
  · rw [if_neg hi]
    by_cases heq : β i = p
    · rw [if_pos heq]
      unfold tieShare
      rw [heq]
      have hA : (Finset.univ.filter fun j => j ≠ i ∧ p < β j) = A := by
        ext j
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun hj => ⟨fun h => by simp [h, heq] at hj, hj⟩⟩
      have hT : (Finset.univ.filter fun j => j ≠ i ∧ β j = p) = T.erase i := by
        ext j
        simp [T]
      have hiT : i ∈ T := by simp [T, heq]
      have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨i, hiT⟩
      have hDen : (1 : ℝ) + ((T.erase i).card : ℝ) = T.card := by
        exact_mod_cast (by rw [Finset.card_erase_of_mem hiT]; omega : 1 + (T.erase i).card = T.card)
      rw [hA, hT, hDen]
      have hNum : 0 ≤ (k : ℝ) - A.card := sub_nonneg.mpr (by exact_mod_cast hlo.le)
      rw [max_eq_left hNum]
      apply min_eq_left
      apply (div_le_one (by exact_mod_cast hTpos)).2
      have hs : (k : ℝ) ≤ (A.card : ℝ) + T.card := by exact_mod_cast (hhi.trans_eq hsplit)
      linarith
    · rw [if_neg heq]
      have hlt : β i < p := lt_of_le_of_ne (le_of_not_gt hi) heq
      have hsub : Finset.univ.filter (fun j => p ≤ β j) ⊆
          Finset.univ.filter (fun j => j ≠ i ∧ β i < β j) := by
        intro j hj
        have hj' := (Finset.mem_filter.mp hj).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          ⟨fun h => (not_le_of_gt hlt) (h ▸ hj'), hlt.trans_le hj'⟩⟩
      have hcard := hhi.trans (Finset.card_le_card hsub)
      unfold tieShare
      rw [max_eq_right (sub_nonpos.mpr (by exact_mod_cast hcard)), zero_div, min_eq_left zero_le_one]

theorem sum_tieShare {n : ℕ} (k : ℕ) (β : Fin n → ℝ) (hkn : k ≤ n) :
    (∑ i, tieShare k i (β i) β) = k := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hz (i : Fin n) : tieShare 0 i (β i) β = 0 := by
      unfold tieShare
      simp only [Nat.cast_zero, zero_sub]
      rw [max_eq_right (neg_nonpos.mpr (by positivity)), zero_div, min_eq_left zero_le_one]
    simp [hz]
  obtain ⟨p, hlo, hhi⟩ := cutoff_exists k β hk hkn
  let a := (Finset.univ.filter fun i => p < β i).card
  let t := (Finset.univ.filter fun i => β i = p).card
  let q := ((k : ℝ) - a) / t
  have ht : 0 < t := by
    have hs := count_split β p
    change a < k at hlo
    change (Finset.univ.filter fun i => p ≤ β i).card = a + t at hs
    omega
  have hEq (i : Fin n) : tieShare k i (β i) β =
      (if p < β i then (1 : ℝ) else 0) + (if β i = p then q else 0) := by
    rw [tieShare_formula k β p hlo hhi]
    by_cases h : p < β i
    · simp [h, ne_of_gt h]
    · simp [h, q, a, t]
  simp_rw [hEq]
  rw [Finset.sum_add_distrib, Finset.sum_boole, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  change (a : ℝ) + (t : ℝ) * (((k : ℝ) - a) / t) = k
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring



theorem sum_tieShare_le_supply {n : ℕ} (k : ℕ) (β : Fin n → ℝ) :
    (∑ i, tieShare k i (β i) β) = (min k n : ℕ) := by
  by_cases h : k ≤ n
  · rw [min_eq_left h]
    exact sum_tieShare k β h
  · have hkn : (n : ℝ) < k := by exact_mod_cast lt_of_not_ge h
    rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
    have hOne (i : Fin n) : tieShare k i (β i) β = 1 := by
      classical
      apply min_eq_right
      let A := Finset.univ.filter fun j => j ≠ i ∧ β i < β j
      let T := Finset.univ.filter fun j => j ≠ i ∧ β j = β i
      have hd : Disjoint A T := by
        rw [Finset.disjoint_left]
        intro j hj ht
        exact (ne_of_gt (Finset.mem_filter.mp hj).2.2) (Finset.mem_filter.mp ht).2.2
      have hc := Finset.card_le_card (show A ∪ T ⊆ (Finset.univ : Finset (Fin n)).erase i from by
        intro j hj
        rcases Finset.mem_union.mp hj with hj | hj
        · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2.1, Finset.mem_univ _⟩
        · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2.1, Finset.mem_univ _⟩)
      rw [Finset.card_union_of_disjoint hd, Finset.card_erase_of_mem (Finset.mem_univ i)] at hc
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
      have hc' : (1 : ℝ) + (A.card : ℝ) + (T.card : ℝ) ≤ n := by
        exact_mod_cast (show 1 + A.card + T.card ≤ n by omega)
      change 1 ≤ max ((k : ℝ) - A.card) 0 / (1 + (T.card : ℝ))
      rw [le_div_iff₀ (by positivity), one_mul]
      exact (show 1 + (T.card : ℝ) ≤ (k : ℝ) - A.card by linarith).trans (le_max_left _ _)
    simp [hOne]

theorem average_bid_ge_of_count {n : ℕ} (k : ℕ) (β : Fin n → ℝ) (hk : 0 < k)
    (hkn : k ≤ n) (b : ℝ) (hc : k ≤ numAbove b β) :
    b < (∑ i, β i * tieShare k i (β i) β) / k := by
  classical
  obtain ⟨p, hp1, hp2⟩ := cutoff_exists k β hk hkn
  have hbp : b < p := by
    by_contra! h
    have hsub : (Finset.univ.filter fun j => b < β j) ⊆
        (Finset.univ.filter fun j => p < β j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h.trans_lt (Finset.mem_filter.mp hj).2⟩
    exact (not_le_of_gt hp1) (hc.trans (Finset.card_le_card hsub))
  have hsum : p * (k : ℝ) ≤ ∑ i, β i * tieShare k i (β i) β := by
    rw [← sum_tieShare k β hkn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : p ≤ β i
    · exact mul_le_mul_of_nonneg_right hi (tieShare_nonneg k i _ _)
    · have hlt := lt_of_not_ge hi
      rw [tieShare_formula k β p hp1 hp2,
        if_neg (not_lt_of_ge hlt.le), if_neg hlt.ne, mul_zero, mul_zero]
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  exact (lt_div_iff₀ hk').2 ((mul_lt_mul_of_pos_right hbp hk').trans_le hsum)

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic
open scoped ProbabilityTheory

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MultiUnitPoA

theorem measurable_tieShare_joint {n : ℕ} (k : ℕ) (i : Fin n) :
    Measurable (fun x : ℝ × (Fin n → ℝ) => tieShare k i x.1 x.2) := by
  classical
  have hEval (j : Fin n) : Measurable (fun x : ℝ × (Fin n → ℝ) => x.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  unfold tieShare
  simp_rw [Finset.natCast_card_filter]
  apply Measurable.min _ measurable_const
  apply Measurable.div
  · apply Measurable.max _ measurable_const
    apply measurable_const.sub
    apply Finset.measurable_sum
    intro j _
    apply measurable_const.piecewise _ measurable_const
    by_cases hj : j = i
    · have hEmpty : {x : ℝ × (Fin n → ℝ) | j ≠ i ∧ x.1 < x.2 j} = ∅ := by
        ext x
        simp [hj]
      exact (congrArg MeasurableSet hEmpty).mpr MeasurableSet.empty
    · have hSet : {x : ℝ × (Fin n → ℝ) | j ≠ i ∧ x.1 < x.2 j} =
          {x : ℝ × (Fin n → ℝ) | x.1 < x.2 j} := by ext x; simp [hj]
      exact (congrArg MeasurableSet hSet).mpr (measurableSet_lt measurable_fst (hEval j))
  · apply measurable_const.add
    apply Finset.measurable_sum
    intro j _
    apply measurable_const.piecewise _ measurable_const
    by_cases hj : j = i
    · have hEmpty : {x : ℝ × (Fin n → ℝ) | j ≠ i ∧ x.2 j = x.1} = ∅ := by
        ext x
        simp [hj]
      exact (congrArg MeasurableSet hEmpty).mpr MeasurableSet.empty
    · have he : MeasurableSet {x : ℝ × (Fin n → ℝ) | x.2 j = x.1} := by
        simpa only [Set.ofPred_and, le_antisymm_iff] using
          (measurableSet_le (hEval j) measurable_fst).inter (measurableSet_le measurable_fst (hEval j))
      have hSet : {x : ℝ × (Fin n → ℝ) | j ≠ i ∧ x.2 j = x.1} =
          {x : ℝ × (Fin n → ℝ) | x.2 j = x.1} := by ext x; simp [hj]
      exact (congrArg MeasurableSet hSet).mpr he

theorem measurable_alloc {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (i : Fin n)
    [∀ j, IsProbabilityMeasure (marginalBid V E j)] : Measurable (alloc k V E i) :=
  (measurable_tieShare_joint k i).stronglyMeasurable.integral_prod_right'.measurable

theorem tieShare_congr {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) {β γ : Fin n → ℝ}
    (h : ∀ j, j ≠ i → β j = γ j) : tieShare k i b β = tieShare k i b γ := by
  classical
  unfold tieShare
  have hgt : (Finset.univ.filter fun j => j ≠ i ∧ b < β j) =
      (Finset.univ.filter fun j => j ≠ i ∧ b < γ j) := by
    ext j
    by_cases hj : j = i <;> simp [hj, h j]
  have heq : (Finset.univ.filter fun j => j ≠ i ∧ β j = b) =
      (Finset.univ.filter fun j => j ≠ i ∧ γ j = b) := by
    ext j
    by_cases hj : j = i <;> simp [hj, h j]
  rw [hgt, heq]

noncomputable def pairLaw {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (i : Fin n) : Measure (ℝ × ℝ) := V i ⊗ₘ E i

theorem pairLaw_probability {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (i : Fin n) :
    IsProbabilityMeasure (pairLaw V E i) := by
  let := hV i
  let := (hE i).1
  unfold pairLaw
  infer_instance

theorem pairLaw_map_fst {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (i : Fin n) [IsProbabilityMeasure (V i)] [IsMarkovKernel (E i)] :
    (pairLaw V E i).map Prod.fst = V i := Measure.fst_compProd (V i) (E i)

theorem pairLaw_map_snd {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (i : Fin n) [IsProbabilityMeasure (V i)] [IsMarkovKernel (E i)] :
    (pairLaw V E i).map Prod.snd = marginalBid V E i := Measure.snd_compProd (V i) (E i)

theorem measurable_fst_profile {n : ℕ} :
    Measurable (fun x : Fin n → ℝ × ℝ => fun i => (x i).1) :=
  measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i))

theorem measurable_snd_profile {n : ℕ} :
    Measurable (fun x : Fin n → ℝ × ℝ => fun i => (x i).2) :=
  measurable_pi_lambda _ (fun i => measurable_snd.comp (measurable_pi_apply i))

theorem measurable_profile_tieShare {n : ℕ} (k : ℕ) (i : Fin n) :
    Measurable (fun x : Fin n → ℝ × ℝ => tieShare k i (x i).2 (fun j => (x j).2)) := by
  have h₀ : Measurable (fun x : Fin n → ℝ × ℝ => (x i).2) :=
    measurable_snd.comp (measurable_pi_apply i)
  have h₁ : Measurable (fun x : Fin n → ℝ × ℝ => fun j => (x j).2) :=
    measurable_snd_profile
  have h₂ : Measurable (fun x : Fin n → ℝ × ℝ => ((x i).2, fun j => (x j).2)) :=
    h₀.prodMk h₁
  apply Measurable.comp (f := fun x : Fin n → ℝ × ℝ => ((x i).2, fun j => (x j).2))
    (g := fun p : ℝ × (Fin n → ℝ) => tieShare k i p.1 p.2)
  · exact measurable_tieShare_joint k i
  · exact h₂

theorem pairProfile_map_fst {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) :
    (Measure.pi (pairLaw V E)).map (fun x i => (x i).1) = Measure.pi V := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  let : ∀ i, IsMarkovKernel (E i) := fun i => (hE i).1
  let : ∀ i, IsProbabilityMeasure (pairLaw V E i) := pairLaw_probability hV hE
  let : ∀ i, SigmaFinite ((pairLaw V E i).map Prod.fst) := fun i => by
    rw [pairLaw_map_fst V E i]
    infer_instance
  rw [Measure.pi_map_pi (f := fun _ => Prod.fst) (fun _ => measurable_fst.aemeasurable)]
  simp_rw [pairLaw_map_fst]

theorem pairProfile_map_snd {n : ℕ} (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) :
    (Measure.pi (pairLaw V E)).map (fun x i => (x i).2) = Measure.pi (marginalBid V E) := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  let : ∀ i, IsMarkovKernel (E i) := fun i => (hE i).1
  let : ∀ i, IsProbabilityMeasure (pairLaw V E i) := pairLaw_probability hV hE
  let : ∀ i, SigmaFinite ((pairLaw V E i).map Prod.snd) := fun i => by
    rw [pairLaw_map_snd V E i]
    let := marginalBid_probability hV hE i
    infer_instance
  rw [Measure.pi_map_pi (f := fun _ => Prod.snd) (fun _ => measurable_snd.aemeasurable)]
  simp_rw [pairLaw_map_snd]

private theorem tieShare_split {n : ℕ} (k : ℕ) (i : Fin (n + 1)) (b x : ℝ)
    (β : Fin n → ℝ) :
    tieShare k i b (i.insertNth (α := fun _ => ℝ) x β) =
      tieShare k i b (i.insertNth (α := fun _ => ℝ) 0 β) := by
  apply tieShare_congr
  intro j hj
  obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
  simp only [Fin.insertNth_apply_succAbove]

private theorem insertNth_snd {n : ℕ} (i : Fin (n + 1)) (x : ℝ × ℝ) (β : Fin n → ℝ × ℝ) :
    (fun j => (i.insertNth (α := fun _ => ℝ × ℝ) x β j).2) =
      i.insertNth (α := fun _ => ℝ) x.2 (fun j => (β j).2) := by
  ext j
  apply (i.forall_iff_succAbove (P := fun j =>
    (i.insertNth (α := fun _ => ℝ × ℝ) x β j).2 =
      i.insertNth (α := fun _ => ℝ) x.2 (fun j => (β j).2) j)).2
  exact ⟨by simp, fun l => by simp only [Fin.insertNth_apply_succAbove]⟩

private theorem alloc_split {n : ℕ} (k : ℕ) (μ : Fin (n + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] (i : Fin (n + 1)) (b : ℝ) :
    allocOf k μ i b =
      ∫ β, tieShare k i b (i.insertNth (α := fun _ => ℝ) 0 β)
        ∂Measure.pi (fun j => μ (i.succAbove j)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he := measurePreserving_piFinSuccAbove μ i
  unfold allocOf
  rw [← he.symm e |>.integral_comp' (tieShare k i b)]
  simp_rw [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, tieShare_split]
  rw [integral_fun_snd (μ := μ i) (ν := Measure.pi fun j => μ (i.succAbove j))
    (fun β => tieShare k i b (i.insertNth (α := fun _ => ℝ) 0 β))]
  simp

set_option maxHeartbeats 650000 in
theorem integrate_allocation {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    (i : Fin n) (f : ℝ × ℝ → ℝ)
    (hi : Integrable (fun x : Fin n → ℝ × ℝ => f (x i) *
      tieShare k i (x i).2 (fun j => (x j).2)) (Measure.pi (pairLaw V E))) :
    (∫ x, f (x i) * tieShare k i (x i).2 (fun j => (x j).2) ∂Measure.pi (pairLaw V E)) =
      ∫ p, f p * alloc k V E i p.2 ∂pairLaw V E i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let := fun j => hV j
    let := fun j => (hE j).1
    let := fun j => pairLaw_probability hV hE j
    let := fun j => marginalBid_probability hV hE j
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ × ℝ) i
    have he := (measurePreserving_piFinSuccAbove (pairLaw V E) i).symm e
    let g (x : Fin (n + 1) → ℝ × ℝ) :=
      f (x i) * tieShare k i (x i).2 (fun j => (x j).2)
    change (∫ x, g x ∂Measure.pi (pairLaw V E)) = _
    rw [← he.integral_comp' g]
    rw [integral_prod (fun x => g (e.symm x)) (he.integrable_comp_of_integrable hi)]
    apply integral_congr_ae
    filter_upwards with p
    simp_rw [g, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same, insertNth_snd, tieShare_split]
    rw [integral_const_mul]
    congr 1
    rw [alloc, alloc_split k (marginalBid V E) i p.2]
    let other : (Fin n → ℝ × ℝ) → (Fin n → ℝ) := fun β j => (β j).2
    have hMap :
        (Measure.pi (fun j : Fin n => pairLaw V E (i.succAbove j))).map other =
          Measure.pi (fun j : Fin n => marginalBid V E (i.succAbove j)) := by
      let : ∀ j : Fin n, SigmaFinite ((pairLaw V E (i.succAbove j)).map Prod.snd) :=
        fun j => by rw [pairLaw_map_snd V E (i.succAbove j)]; infer_instance
      rw [Measure.pi_map_pi (f := fun _ => Prod.snd) (fun _ => measurable_snd.aemeasurable)]
      simp_rw [pairLaw_map_snd]
    let F (β : Fin n → ℝ) := tieShare k i p.2 (i.insertNth (α := fun _ => ℝ) 0 β)
    have hIns : Measurable (i.insertNth (α := fun _ => ℝ) (0 : ℝ)) := by
      apply measurable_pi_lambda
      intro j
      by_cases hj : j = i
      · subst j
        simp only [Fin.insertNth_apply_same]
        exact measurable_const
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
        simp only [Fin.insertNth_apply_succAbove]
        exact measurable_pi_apply l
    have hPair : Measurable (fun β : Fin n → ℝ =>
        (p.2, i.insertNth (α := fun _ => ℝ) (0 : ℝ) β)) := measurable_const.prodMk hIns
    have hF : Measurable F := by
      apply Measurable.comp (g := fun x : ℝ × (Fin (n + 1) → ℝ) => tieShare k i x.1 x.2)
        (f := fun β : Fin n → ℝ => (p.2, i.insertNth (α := fun _ => ℝ) (0 : ℝ) β))
      · exact measurable_tieShare_joint k i
      · exact hPair
    let M := Measure.pi (fun j : Fin n => pairLaw V E (i.succAbove j))
    have hOther : Measurable other := measurable_snd_profile
    have hInt := integral_map (μ := M) (f := F) hOther.aemeasurable hF.aestronglyMeasurable
    change (∫ β, F (other β) ∂M) = _
    rw [← hInt]
    rw [show M.map other = _ from hMap]

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Theorem3Counterexample

noncomputable def V (_i : Fin 2) : Measure ℝ := Measure.dirac (-4)
noncomputable def E (_i : Fin 2) : Kernel ℝ ℝ := Kernel.deterministic (fun _ => 0) measurable_const

private theorem hV : IsValueProfile V := fun i => by unfold V; infer_instance

private theorem hE : IsStrategyProfile E := by
  intro i
  constructor
  · unfold E
    infer_instance
  · intro v
    change Measure.dirac (0 : ℝ) (Iio 0) = 0
    rw [Measure.dirac_apply' _ measurableSet_Iio]
    simp

private theorem mem_support_value {v : ℝ} (hs : v ∈ (V 0).support) : v = -4 := by
  have ht : ({(-4 : ℝ)} : Set ℝ) ∈ ae (V 0) := by simp [V, ae_dirac_eq]
  exact (Measure.support_subset_of_isClosed isClosed_singleton ht hs : v ∈ {(-4 : ℝ)})

private theorem value_in_support (i : Fin 2) : (-4 : ℝ) ∈ (V i).support := by
  have h : ∀ᵐ v ∂V i, v ∈ (V i).support := Measure.support_mem_ae
  rwa [V, ae_dirac_eq, eventually_pure] at h

private theorem marginal_dirac (Et : Fin 2 → Kernel ℝ ℝ) (i : Fin 2) :
    marginalBid V Et i = Et i (-4) := by
  rw [marginalBid, V, Measure.dirac_bind (Et i).measurable]

private theorem bid_profile_ae_zero :
    ∀ᵐ β ∂Measure.pi (marginalBid V E), β = (fun _ : Fin 2 => 0) := by
  have h (i : Fin 2) : ∀ᵐ b ∂marginalBid V E i, b = (0 : ℝ) := by
    rw [marginal_dirac]
    simp [E, Kernel.deterministic_apply, ae_dirac_eq]
  let : ∀ i, IsProbabilityMeasure (marginalBid V E i) := marginalBid_probability hV hE
  exact (eventually_all.mpr fun i => (Measure.tendsto_eval_ae_ae (i := i)).eventually (h i)).mono
    fun _ hh => funext hh

private theorem alloc_original (i : Fin 2) (b : ℝ) (hb : 0 ≤ b) :
    alloc 1 V E i b = if b = 0 then 1 / 2 else 1 := by
  let : ∀ j, IsProbabilityMeasure (marginalBid V E j) := marginalBid_probability hV hE
  unfold alloc allocOf
  rw [integral_congr_ae (bid_profile_ae_zero.mono
    (fun x hx => show tieShare 1 i b x = tieShare 1 i b (fun _ => 0) from congrArg _ hx))]
  simp only [integral_const, probReal_univ, one_smul]
  have hAbove : (Finset.univ.filter fun j : Fin 2 => j ≠ i ∧ b < (0 : ℝ)).card = 0 := by
    simp [not_lt_of_ge hb]
  have hTie : (Finset.univ.filter fun j : Fin 2 => j ≠ i ∧ (0 : ℝ) = b) =
      if b = 0 then Finset.univ.erase i else ∅ := by
    ext j
    by_cases h : b = 0
    · simp [h]
    · simp [h, Ne.symm h]
  unfold tieShare
  rw [hAbove, hTie]
  by_cases h : b = 0
  · rw [if_pos h]
    norm_num [h, Finset.card_erase_of_mem (Finset.mem_univ i)]
  · norm_num [h]

private theorem initial_bne : IsApproxBNE 1 V E 0 := by
  intro i v hv
  have hv' : v = -4 := mem_support_value (by exact hv)
  subst v
  change Integrable (utility 1 V E i (-4)) (E i (-4)) ∧ _
  rw [show E i (-4) = Measure.dirac 0 from rfl]
  refine ⟨integrable_dirac (by simp), ?_⟩
  intro b hb
  rw [integral_dirac]
  unfold utility
  rw [alloc_original i b hb, alloc_original i 0 le_rfl]
  by_cases h : b = 0
  · subst b
    norm_num
  · simp [h]
    linarith

private theorem alloc_zero_of_atomless (Et : Fin 2 → Kernel ℝ ℝ)
    (hEt : IsStrategyProfile Et) (hA : IsAtomless V Et) (i : Fin 2) :
    alloc 1 V Et i 0 = 0 := by
  let : ∀ j, IsProbabilityMeasure (marginalBid V Et j) := marginalBid_probability hV hEt
  have hPositive (j : Fin 2) : ∀ᵐ b ∂marginalBid V Et j, 0 < b := by
    rw [ae_iff]
    simp only [not_lt]
    have he : Iio (0 : ℝ) ∪ {0} = Iic 0 := by
      ext x
      simp [le_iff_lt_or_eq]
    change marginalBid V Et j (Iic 0) = 0
    rw [← he]
    exact measure_union_null (marginalBid_negative_zero hEt j) (hA j 0)
  have hAEP : ∀ᵐ β ∂Measure.pi (marginalBid V Et), ∀ j, 0 < β j :=
    eventually_all.mpr fun j => (Measure.tendsto_eval_ae_ae (i := j)).eventually (hPositive j)
  unfold alloc allocOf
  calc
    _ = ∫ _ : Fin 2 → ℝ, (0 : ℝ) ∂Measure.pi (marginalBid V Et) := by
      apply integral_congr_ae
      filter_upwards [hAEP] with β hβ
      obtain ⟨j, hj⟩ : ∃ j : Fin 2, j ≠ i := by
        fin_cases i
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
      have hc : 1 ≤ (Finset.univ.filter fun j => j ≠ i ∧ (0 : ℝ) < β j).card :=
        Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj, hβ j⟩⟩
      unfold tieShare
      rw [max_eq_right (sub_nonpos.mpr (by exact_mod_cast hc)), zero_div, min_eq_left zero_le_one]
    _ = 0 := integral_zero _ _

set_option maxHeartbeats 800000 in
theorem counterexample :
    IsValueProfile V ∧ IsStrategyProfile E ∧ IsApproxBNE 1 V E 0 ∧
      ¬ ∃ Et : Fin 2 → Kernel ℝ ℝ, IsStrategyProfile Et ∧
        IsApproxBNE 1 V Et 1 ∧ IsAtomless V Et := by
  refine ⟨hV, hE, initial_bne, ?_⟩
  rintro ⟨Et, hEt, hBNE, hA⟩
  let μ (i : Fin 2) := marginalBid V Et i
  let : ∀ i, IsProbabilityMeasure (μ i) := marginalBid_probability hV hEt
  have hp (i : Fin 2) : ∀ᵐ b ∂μ i, (0 : ℝ) ≤ b := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using marginalBid_negative_zero (V := V) hEt i
  have hInt (i : Fin 2) : Integrable (utility 1 V Et i (-4)) (μ i) := by
    dsimp only [μ]
    rw [marginal_dirac]
    exact (hBNE i (-4) (value_in_support i)).1
  have hLower (i : Fin 2) : -1 ≤ ∫ b, utility 1 V Et i (-4) b ∂μ i := by
    have h := (hBNE i (-4) (value_in_support i)).2 0 le_rfl
    rw [show utility 1 V Et i (-4) 0 = 0 by simp [utility, alloc_zero_of_atomless Et hEt hA]] at h
    dsimp only [μ]
    rw [marginal_dirac]
    simpa using h
  have hUpper (i : Fin 2) : (∫ b, utility 1 V Et i (-4) b ∂μ i) ≤
      -4 * ∫ b, alloc 1 V Et i b ∂μ i := by
    rw [← integral_const_mul]
    have hI : Integrable (alloc 1 V Et i) (μ i) := by
      apply (integrable_const (1 : ℝ)).mono' (measurable_alloc 1 V Et i).aestronglyMeasurable
      exact Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs, abs_of_nonneg (alloc_nonneg 1 i b)]
        exact alloc_le_one 1 i b
    apply integral_mono_ae (hInt i) (hI.const_mul _)
    filter_upwards [hp i] with b hb
    exact mul_le_mul_of_nonneg_right (by linarith : (-4 : ℝ) - b ≤ -4) (alloc_nonneg 1 i b)
  have hAlloc (i : Fin 2) : (∫ b, alloc 1 V Et i b ∂μ i) =
      ∫ x, tieShare 1 i (x i).2 (fun j => (x j).2) ∂Measure.pi (pairLaw V Et) := by
    let : ∀ j, IsProbabilityMeasure (pairLaw V Et j) := pairLaw_probability hV hEt
    have hm := measurable_profile_tieShare 1 i
    have hI : Integrable (fun x : Fin 2 → ℝ × ℝ => tieShare 1 i (x i).2 (fun j => (x j).2))
        (Measure.pi (pairLaw V Et)) := by
      apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tieShare_nonneg 1 i _ _)]
        exact tieShare_le_one 1 i _ _
    rw [show (∫ x, tieShare 1 i (x i).2 (fun j => (x j).2) ∂Measure.pi (pairLaw V Et)) =
        ∫ p, alloc 1 V Et i p.2 ∂pairLaw V Et i from by
      simpa only [one_mul] using integrate_allocation 1 V Et hV hEt i
        (fun _ => 1) (by simpa only [one_mul] using hI)]
    let := hV i
    let := (hEt i).1
    dsimp only [μ]
    rw [← pairLaw_map_snd V Et i]
    exact integral_map measurable_snd.aemeasurable (measurable_alloc 1 V Et i).aestronglyMeasurable
  have hSum : (∑ i, ∫ b, alloc 1 V Et i b ∂μ i) = 1 := by
    let : ∀ j, IsProbabilityMeasure (pairLaw V Et j) := pairLaw_probability hV hEt
    have hI (i : Fin 2) : Integrable
        (fun x : Fin 2 → ℝ × ℝ => tieShare 1 i (x i).2 (fun j => (x j).2))
        (Measure.pi (pairLaw V Et)) := by
      have hm := measurable_profile_tieShare 1 i
      apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tieShare_nonneg 1 i _ _)]
        exact tieShare_le_one 1 i _ _
    simp_rw [hAlloc]
    rw [← integral_finsetSum _ (fun i _ => hI i)]
    simp_rw [sum_tieShare 1 _ (by decide : 1 ≤ 2)]
    simp
  have h0 := (hLower 0).trans (hUpper 0)
  have h1 := (hLower 1).trans (hUpper 1)
  rw [Fin.sum_univ_two] at hSum
  linarith

end Theorem3Counterexample

theorem solution : ¬ (∀ {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) (ε : ℝ),
    IsValueProfile V → IsStrategyProfile E → IsApproxBNE k V E ε →
    ∀ ω : ℝ, 0 < ω →
      ∃ Et : Fin n → Kernel ℝ ℝ, IsStrategyProfile Et ∧
        IsApproxBNE k V Et (ε + ω) ∧
        IsAtomless V Et ∧ welfare k V E = welfare k V Et ∧
        (∀ i v t, E i v (Set.Iic t) = 1 → Et i v (Set.Iic (t + ω)) = 1)) := by
  intro h
  obtain ⟨hV, hE, hB, hnot⟩ := Theorem3Counterexample.counterexample
  obtain ⟨Et, hEt, hBEt, hA, _⟩ :=
    h 1 Theorem3Counterexample.V Theorem3Counterexample.E 0 hV hE hB 1 zero_lt_one
  exact hnot ⟨Et, hEt, by simpa using hBEt, hA⟩

#print axioms solution
