-- Prove2me | solution 1 for LargeSupplyFPA.Asymptotic.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T14:03:38.738412+00:00
-- url     : https://prove2.me/submissions/ab9212c9-09d8-40b9-aa1c-94b705af79b4

import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing

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

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false


theorem solution (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (lo hi : ℕ → ℝ) (hpair : ∀ k, lo k ≤ hi k)
    (hlo : ∀ k, 0 ≤ lo k ∧ lo k ≤ lowThreshold δ k (V k) (E k))
    (hhi : ∀ k, highThreshold δ k (V k) (E k) ≤ hi k) :
    IsExtremizing n V E lo hi id := by
  refine ⟨fun _ _ h => h, fun k => ⟨(hlo k).1, hpair k⟩, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_tail_error δ hδ.1) ?_ ?_
    · exact Filter.Eventually.of_forall fun _ => measureReal_nonneg
    · filter_upwards [eventually_threshold_scale δ hδ] with k hk
      let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
      exact kthBidCDF_low_bound δ k (hseq.1 k) (hseq.2.2 k) (hA4 k) (lo k) (hlo k)
        hk.1 hk.2.1
  · have hComplement : Tendsto (fun k => 1 - kthBidCDF k (V k) (E k) (hi k)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_tail_error δ hδ.1) ?_ ?_
      · apply Filter.Eventually.of_forall
        intro k
        let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
        exact sub_nonneg.mpr measureReal_le_one
      · filter_upwards [eventually_threshold_scale δ hδ] with k hk
        let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
        exact kthBidCDF_high_bound δ k (hA4 k) (hi k) (hhi k) hk.1 hk.2.2
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hComplement

#print axioms solution
