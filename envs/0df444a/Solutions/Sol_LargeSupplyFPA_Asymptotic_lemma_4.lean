-- Prove2me | solution 1 for LargeSupplyFPA.Asymptotic.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T14:03:38.807188+00:00
-- url     : https://prove2.me/submissions/3c2fc069-045a-412f-a89a-01fa8cf051f4

import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model

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
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

namespace MultiUnitPoA

theorem threshold_nonneg {f : ℝ → ℝ} {q : ℝ} :
    0 ≤ sInf {b : ℝ | 0 ≤ b ∧ f b ≤ q} :=
  Real.sInf_nonneg (fun _ hb => hb.1)

theorem lowThreshold_le_highThreshold (δ : ℝ) {n : ℕ} (k : ℕ)
    (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (hHigh : {b : ℝ | 0 ≤ b ∧
      expNumAbove V E b ≤ (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1}.Nonempty) :
    lowThreshold δ k V E ≤ highThreshold δ k V E := by
  apply le_csInf hHigh
  intro b hb
  apply csInf_le ⟨0, fun _ hx => hx.1⟩
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hpow : 0 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ) := by positivity
  linarith

private theorem deviation_le_optUtility {n : ℕ} {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} (k : ℕ) (i : Fin n) (v d : ℝ) (hd : 0 ≤ d)
    (hAlloc : ∀ b : ℝ, 0 ≤ alloc k V E i b ∧ alloc k V E i b ≤ 1) :
    utility k V E i v d ≤ optUtility k V E i v := by
  unfold optUtility
  refine le_ciSup (f := fun bid : Set.Ici (0 : ℝ) => utility k V E i v bid.val) ?_ ⟨d, hd⟩
  refine ⟨max v 0, ?_⟩
  rintro _ ⟨bid, rfl⟩
  unfold utility
  rcases le_or_gt v bid.val with hv | hv
  · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (hAlloc _).1).trans
      (le_max_right _ _)
  · exact (mul_le_of_le_one_right (sub_nonneg.mpr hv.le) (hAlloc _).2).trans
      ((sub_le_self _ bid.property).trans (le_max_left _ _))

/-- The compactness and utility argument in Lemma 4. Its bid-count and allocation
inputs can be supplied by the mission's preceding milestones. -/
theorem positive_utility_interval (δ : ℝ) (H : ℝ) (n : ℕ → ℕ)
    (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (s : ℕ → ℕ) (hs : StrictMono s) (c : ℝ) (hc : 0 < c)
    (hOrder : ∀ᶠ k in atTop, lowThreshold δ k (V k) (E k) ≤ highThreshold δ k (V k) (E k))
    (hBound : ∀ᶠ k in atTop, highThreshold δ k (V k) (E k) ≤ H + 1)
    (hLo : Tendsto (fun k => kthBidCDF k (V k) (E k) (lowThreshold δ k (V k) (E k)))
      atTop (𝓝 0))
    (hHi : Tendsto (fun k => kthBidCDF k (V k) (E k) (highThreshold δ k (V k) (E k)))
      atTop (𝓝 1))
    (hCDF : ∀ k d, 0 ≤ kthBidCDF k (V k) (E k) d ∧ kthBidCDF k (V k) (E k) d ≤ 1)
    (hAlloc : ∀ k i d, 0 ≤ alloc k (V k) (E k) i d ∧ alloc k (V k) (E k) i d ≤ 1)
    (hFact3 : ∀ k i d, 0 ≤ d → kthBidCDF k (V k) (E k) d ≤ alloc k (V k) (E k) i d)
    (hwide : ∀ (lo hi : ℕ → ℝ) (θ : ℕ → ℕ), StrictMono θ → IsExtremizing n V E lo hi (s ∘ θ) →
      ∀ L : ℝ, Tendsto (fun l => hi (s (θ l)) - lo (s (θ l))) atTop (𝓝 L) → c < L) :
    ∃ ubar : ℝ, 0 < ubar ∧ ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ mstar : ℕ, ∀ m : ℕ, mstar < m →
      ∃ a b : ℝ, lowThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) < a ∧ a + c / 8 ≤ b ∧
        b < highThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) ∧
        ∀ i : Fin (n (s (θ m))), ∀ v ∈ Set.Icc a b,
          ubar ≤ optUtility (s (θ m)) (V (s (θ m))) (E (s (θ m))) i v := by
  let lo : ℕ → ℝ := fun k => lowThreshold δ k (V k) (E k)
  let hi : ℕ → ℝ := fun k => highThreshold δ k (V k) (E k)
  let orderedLo : ℕ → ℝ := fun k => min (lo k) (hi k)
  let d : ℕ → ℝ := fun k => max (hi k - c / 2) 0
  have hlo0 (k : ℕ) : 0 ≤ lo k := threshold_nonneg
  have hhi0 (k : ℕ) : 0 ≤ hi k := threshold_nonneg
  have hord : ∀ᶠ k in atTop, orderedLo k = lo k :=
    hOrder.mono fun k hk => min_eq_left hk
  have hLo' : Tendsto (fun k => kthBidCDF k (V k) (E k) (orderedLo k)) atTop (𝓝 0) := by
    apply hLo.congr'
    filter_upwards [hord] with k hk
    change kthBidCDF k (V k) (E k) (lo k) = kthBidCDF k (V k) (E k) (orderedLo k)
    rw [hk]
  have hWidths : ∀ᶠ k in atTop, hi k - orderedLo k ∈ Set.Icc (0 : ℝ) (H + 1) := by
    filter_upwards [hBound] with k hk
    have h0 : 0 ≤ orderedLo k := le_min (hlo0 k) (hhi0 k)
    exact ⟨sub_nonneg.mpr (min_le_right _ _), (sub_le_self _ h0).trans hk⟩
  obtain ⟨L, _, θ, hθ, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := H + 1)).tendsto_subseq'
    ((hs.tendsto_atTop.eventually hWidths).frequently)
  have hφ : StrictMono (s ∘ θ) := hs.comp hθ
  have hExt : IsExtremizing n V E orderedLo hi (s ∘ θ) :=
    ⟨hφ, fun k => ⟨le_min (hlo0 k) (hhi0 k), min_le_right _ _⟩,
      hLo'.comp hφ.tendsto_atTop, hHi.comp hφ.tendsto_atTop⟩
  have hLc := hwide orderedLo hi θ hθ hExt L hL
  have hGap : ∀ᶠ m in atTop, c < hi (s (θ m)) - lo (s (θ m)) := by
    filter_upwards [hL.eventually (eventually_gt_nhds hLc), hφ.tendsto_atTop.eventually hord]
      with m hm ho
    change c < hi (s (θ m)) - orderedLo (s (θ m)) at hm
    change orderedLo (s (θ m)) = lo (s (θ m)) at ho
    rwa [ho] at hm
  let prob : ℕ → ℝ := fun k => kthBidCDF k (V k) (E k) (d k)
  obtain ⟨p, hp, ρ, hρ, hProb⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).tendsto_subseq
    (x := prob ∘ s ∘ θ) (fun m => hCDF (s (θ m)) (d (s (θ m))))
  let τε := θ ∘ ρ
  have hτε : StrictMono τε := hθ.comp hρ
  have hτεs : StrictMono (s ∘ τε) := hs.comp hτε
  have hGap' : ∀ᶠ m in atTop, c < hi (s (τε m)) - lo (s (τε m)) :=
    hρ.tendsto_atTop.eventually hGap
  have hd (k : ℕ) : 0 ≤ d k := le_max_right _ _
  have hdhi (k : ℕ) : d k ≤ hi k := max_le (by linarith) (hhi0 k)
  have hdEq : ∀ᶠ m in atTop, d (s (τε m)) = hi (s (τε m)) - c / 2 := by
    filter_upwards [hGap'] with m hm
    exact max_eq_left (by linarith [hlo0 (s (τε m))])
  have hp0 : 0 < p := by
    by_contra! hn
    have hpz : p = 0 := le_antisymm hn hp.1
    have hExt' : IsExtremizing n V E d hi (s ∘ τε) :=
      ⟨hτεs, fun k => ⟨hd k, hdhi k⟩, hpz ▸ hProb, hHi.comp hτεs.tendsto_atTop⟩
    have hWidth : Tendsto (fun l => hi (s (τε l)) - d (s (τε l))) atTop (𝓝 (c / 2)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hdEq] with m hm
      rw [hm]
      ring
    linarith [hwide d hi τε hτε hExt' (c / 2) hWidth]
  have hpHalf : p / 2 < p := by linarith
  have hProb' : ∀ᶠ m in atTop, p / 2 < prob (s (τε m)) :=
    hProb.eventually (eventually_gt_nhds hpHalf)
  obtain ⟨mstar, hmstar⟩ := eventually_atTop.mp (hGap'.and (hdEq.and hProb'))
  refine ⟨c / 4 * (p / 2), by positivity, τε, hτε, mstar, ?_⟩
  intro m hm
  obtain ⟨hgap, hd_eq, hprob⟩ := hmstar m hm.le
  let k := s (τε m)
  refine ⟨hi k - c / 4, hi k - c / 8, ?_, by ring_nf; exact le_rfl, by dsimp [hi, k]; linarith, ?_⟩
  · change lo k < hi k - c / 4
    change c < hi k - lo k at hgap
    linarith
  intro i v hv
  have hSurplus : c / 4 ≤ v - d k := by
    change d k = hi k - c / 2 at hd_eq
    rw [hd_eq]
    linarith [hv.1]
  have hWin : p / 2 ≤ alloc k (V k) (E k) i (d k) :=
    (le_of_lt hprob).trans (hFact3 k i (d k) (hd k))
  calc
    _ ≤ (v - d k) * alloc k (V k) (E k) i (d k) :=
      mul_le_mul hSurplus hWin (by positivity) (by linarith)
    _ ≤ optUtility k (V k) (E k) i v :=
      deviation_le_optUtility k i v (d k) (hd k) (hAlloc k i)

end MultiUnitPoA

open MeasureTheory ProbabilityTheory
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

private theorem measurable_count {n : ℕ} (p : Fin n → (Fin n → ℝ) → Prop)
    [∀ j β, Decidable (p j β)] (hp : ∀ j, MeasurableSet {β | p j β}) :
    Measurable (fun β => ((Finset.univ.filter fun j => p j β).card : ℝ)) := by
  simp_rw [Finset.natCast_card_filter]
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.piecewise (hp j) measurable_const

private theorem measurable_tieShare {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) :
    Measurable (tieShare k i b) := by
  classical
  have hEval (j : Fin n) : Measurable (fun β : Fin n → ℝ => β j) :=
    measurable_pi_apply j
  have hAbove := measurable_count (fun j β => j ≠ i ∧ b < β j) (fun j => by
    by_cases h : j = i
    · simp [h]
    · simpa [h] using
        measurableSet_lt (measurable_const (a := b)) (hEval j))
  have hTie := measurable_count (fun j β => j ≠ i ∧ β j = b) (fun j => by
    by_cases h : j = i
    · simp [h]
    · simpa [h, Set.preimage] using
        (hEval j) (measurableSet_singleton b))
  unfold tieShare
  exact (((measurable_const.sub hAbove).max measurable_const).div
    (measurable_const.add hTie)).min measurable_const

private theorem tieShare_eq_one {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) (β : Fin n → ℝ)
    (h : (Finset.univ.filter fun j => j ≠ i ∧ b ≤ β j).card < k) :
    tieShare k i b β = 1 := by
  classical
  let above := Finset.univ.filter fun j : Fin n => j ≠ i ∧ b < β j
  let tied := Finset.univ.filter fun j : Fin n => j ≠ i ∧ β j = b
  have hdisjoint : Disjoint above tied := by
    rw [Finset.disjoint_left]
    intro j ha ht
    have hlt := (Finset.mem_filter.mp ha).2.2
    have heq := (Finset.mem_filter.mp ht).2.2
    exact (ne_of_gt hlt) heq
  have hunion : above ∪ tied = Finset.univ.filter fun j => j ≠ i ∧ b ≤ β j := by
    ext j
    simp [above, tied, le_iff_lt_or_eq, eq_comm (a := β j), and_or_left]
  have hcount : above.card + tied.card < k := by
    simpa only [← Finset.card_union_of_disjoint hdisjoint, hunion] using h
  have hroom : (1 : ℝ) + tied.card ≤ (k : ℝ) - above.card := by
    have hnat : 1 + tied.card + above.card ≤ k := by omega
    have hreal : (1 : ℝ) + tied.card + above.card ≤ k := by exact_mod_cast hnat
    linarith
  change min (max ((k : ℝ) - above.card) 0 / (1 + tied.card)) 1 = 1
  apply min_eq_right
  rw [le_div_iff₀ (by positivity)]
  rw [one_mul]
  exact hroom.trans (le_max_left _ _)

private theorem cdf_le_alloc_of_event_ae {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) [∀ j, IsProbabilityMeasure (marginalBid V E j)]
    (i : Fin n) (b d : ℝ)
    (h : ∀ᵐ β ∂Measure.pi (marginalBid V E), numAbove b β < k →
      (Finset.univ.filter fun j => j ≠ i ∧ d ≤ β j).card < k) :
    kthBidCDF k V E b ≤ alloc k V E i d := by
  classical
  let μ := Measure.pi (marginalBid V E)
  let event : Set (Fin n → ℝ) := {β | numAbove b β < k}
  have hcount : Measurable (fun β : Fin n → ℝ => (numAbove b β : ℝ)) :=
    measurable_count (fun j β => b < β j) (fun j =>
      measurableSet_lt measurable_const (measurable_pi_apply j))
  have hevent : MeasurableSet event := by
    simpa only [event, Nat.cast_lt] using measurableSet_lt hcount
      (measurable_const (a := (k : ℝ)))
  have hnonneg (β : Fin n → ℝ) : 0 ≤ tieShare k i d β := by
    unfold tieShare
    exact le_min (div_nonneg (le_max_right _ _) (by positivity)) zero_le_one
  have hbounded (β : Fin n → ℝ) : tieShare k i d β ≤ 1 := by
    unfold tieShare
    exact min_le_right _ _
  have hint : Integrable (tieShare k i d) μ :=
    (integrable_const (1 : ℝ)).mono'
      (measurable_tieShare k i d).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg β)]
        exact hbounded β)
  change μ.real event ≤ ∫ β, tieShare k i d β ∂μ
  rw [← integral_indicator_one hevent]
  apply integral_mono_ae ((integrable_const (1 : ℝ)).indicator hevent) hint
  filter_upwards [h] with β hβ
  by_cases hb : β ∈ event
  · simp [hb, tieShare_eq_one k i d β (hβ hb)]
  · simpa [hb] using hnonneg β

namespace Fact3

theorem solution {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (b : ℝ) (_hb : 0 ≤ b) (i : Fin n) :
    (∀ Δ : ℝ, 0 < Δ → kthBidCDF k V E b ≤ alloc k V E i (b + Δ)) ∧
      (IsAtomless V E → kthBidCDF k V E b ≤ alloc k V E i b) := by
  classical
  let (j : Fin n) : IsProbabilityMeasure (marginalBid V E j) := by
    let hk := (hE j).1
    let hv := hV j
    exact isProbabilityMeasure_bind (E j).aemeasurable
      (Filter.Eventually.of_forall fun _ => inferInstance)
  constructor
  · intro Δ hΔ
    apply cdf_le_alloc_of_event_ae
    apply Filter.Eventually.of_forall
    intro β hβ
    refine lt_of_le_of_lt (Finset.card_le_card ?_) hβ
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
      (lt_add_of_pos_right b hΔ).trans_le (Finset.mem_filter.mp hj).2.2⟩
  · intro hatomless
    have hne (j : Fin n) : ∀ᵐ β ∂Measure.pi (marginalBid V E), β j ≠ b := by
      rw [ae_iff]
      simpa only [not_not, Set.preimage, Set.mem_singleton_iff, Function.eval] using
        Measure.pi_eval_preimage_null (marginalBid V E) (hatomless j b)
    apply cdf_le_alloc_of_event_ae
    filter_upwards [ae_all_iff.mpr hne] with β hβ hcount
    refine lt_of_le_of_lt (Finset.card_le_card ?_) hcount
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
      lt_of_le_of_ne (Finset.mem_filter.mp hj).2.2 (hβ j).symm⟩


end Fact3

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

private theorem marginalBid_Ioi_eq_zero {n : ℕ} (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (i : Fin n) [IsProbabilityMeasure (V i)]
    [IsMarkovKernel (E i)] {H ω b : ℝ} (hValue : V i (Set.Icc 0 H) = 1)
    (hBid : OverbidAtMost ω V E) (hb : H + ω ≤ b) :
    marginalBid V E i (Set.Ioi b) = 0 := by
  have hValues : ∀ᵐ v ∂V i, v ∈ Set.Icc (0 : ℝ) H :=
    (ae_mem_iff_measure_eq measurableSet_Icc.nullMeasurableSet).2
      (hValue.trans (measure_univ (μ := V i)).symm)
  have hzero : (fun v => E i v (Set.Ioi b)) =ᵐ[V i] 0 := by
    filter_upwards [hValues, Measure.support_mem_ae (μ := V i)] with v hv hs
    have hmass := hBid i v hs
    have hcompl : E i v (Set.Iic (v + ω))ᶜ = 0 := by
      rw [measure_compl measurableSet_Iic (by finiteness), hmass, measure_univ, tsub_self]
    refine measure_mono_null (s := Set.Ioi b) ?_ hcompl
    intro x hx hle
    exact not_lt_of_ge (le_trans (show x ≤ v + ω from hle)
      (le_trans (add_le_add_left hv.2 ω) hb)) hx
  rw [marginalBid, Measure.bind_apply measurableSet_Ioi (E i).aemeasurable,
    lintegral_congr_ae hzero]
  simp

private theorem eventually_nonneg_cutoff (δ : ℝ) (hδ : δ < (0.5 : ℝ)) :
    ∀ᶠ k : ℕ in atTop, 0 ≤ (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 := by
  have hExponent : 0 < 1 - ((0.5 : ℝ) + δ) := by linarith
  have hPower := (tendsto_rpow_neg_atTop hExponent).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hPower.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_ge_atTop (2 : ℕ)] with k hSmall hk
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : 0 < (k : ℝ) := by linarith
  have hRewrite : (k : ℝ) ^ ((0.5 : ℝ) + δ) =
      (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) * (k : ℝ) := by
    conv_rhs => rw [← Real.rpow_add_one hkPos.ne']
    congr 1
    ring
  change (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) < 1 / 2 at hSmall
  have hBound := mul_lt_mul_of_pos_right hSmall hkPos
  rw [hRewrite]
  linarith

namespace Lemma3

theorem solution (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5) (H κ : ℝ)
    (hH : 0 < H) (_hκ : 0 < κ) (n : ℕ → ℕ)
    (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hA3 : Assumption3 n V E) (_hA4 : ∀ k, IsAtomless (V k) (E k)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, highThreshold δ k (V k) (E k) ≤ H + η := by
  intro η hη
  obtain ⟨ω, hωpos, hωsmall, hωbid⟩ := hA3
  filter_upwards [hωsmall.bound hη, eventually_nonneg_cutoff δ hδ.2] with k hSmall hCutoff
  have hnk : (k : ℝ) < n k := by exact_mod_cast hseq.1 k
  have hnPos : 0 < (n k : ℝ) := lt_of_le_of_lt (by positivity) hnk
  have hRatio : (k : ℝ) / (n k : ℝ) ≤ 1 := (div_le_one hnPos).2 hnk.le
  have hRatio0 : 0 ≤ (k : ℝ) / (n k : ℝ) := by positivity
  have hωle : ω k ≤ η := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hωpos k), abs_of_nonneg hRatio0] at hSmall
    exact hSmall.trans (mul_le_of_le_one_right hη.le hRatio)
  have hExpected : expNumAbove (V k) (E k) (H + η) = 0 := by
    unfold expNumAbove
    apply Finset.sum_eq_zero
    intro i _
    let hv := hseq.2.1 k i
    let he := (hseq.2.2 k i).1
    rw [Measure.real, marginalBid_Ioi_eq_zero (V k) (E k) i (hA1 k i).1 (hωbid k)
      (add_le_add_right hωle H), ENNReal.toReal_zero]
  unfold highThreshold
  apply csInf_le
  · exact ⟨0, fun _ hb => hb.1⟩
  · exact ⟨by linarith, hExpected ▸ hCutoff⟩


end Lemma3

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Lemma1

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


end Lemma1

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false


theorem solution (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 0.5) (H κ : ℝ)
    (hH : 0 < H) (hκ : 0 < κ) (n : ℕ → ℕ)
    (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hA3 : Assumption3 n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (s : ℕ → ℕ) (hs : StrictMono s) (c : ℝ) (hc : 0 < c)
    (hwide : ∀ (lo hi : ℕ → ℝ) (θ : ℕ → ℕ), StrictMono θ → IsExtremizing n V E lo hi (s ∘ θ) →
      ∀ L : ℝ, Tendsto (fun l => hi (s (θ l)) - lo (s (θ l))) atTop (𝓝 L) → c < L) :
    ∃ ubar : ℝ, 0 < ubar ∧ ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ mstar : ℕ, ∀ m : ℕ, mstar < m →
      ∃ a b : ℝ, lowThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) < a ∧ a + c / 8 ≤ b ∧
        b < highThreshold δ (s (θ m)) (V (s (θ m))) (E (s (θ m))) ∧
        ∀ i : Fin (n (s (θ m))), ∀ v ∈ Set.Icc a b,
          ubar ≤ optUtility (s (θ m)) (V (s (θ m))) (E (s (θ m))) i v := by
  have hOrder : ∀ᶠ k in atTop, lowThreshold δ k (V k) (E k) ≤ highThreshold δ k (V k) (E k) := by
    filter_upwards [eventually_threshold_scale δ hδ] with k hk
    let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
    apply lowThreshold_le_highThreshold
    exact ⟨_, threshold_mem (continuous_expNumAbove (hA4 k)) tendsto_expNumAbove hk.2.2⟩
  let lo : ℕ → ℝ := fun k => lowThreshold δ k (V k) (E k)
  let hi : ℕ → ℝ := fun k => highThreshold δ k (V k) (E k)
  let lo' : ℕ → ℝ := fun k => min (lo k) (hi k)
  have hlo (k : ℕ) : 0 ≤ lo k := threshold_nonneg
  have hhi (k : ℕ) : 0 ≤ hi k := threshold_nonneg
  have hExt := Lemma1.solution δ hδ n V E hseq hA4 lo' hi
      (fun _ => min_le_right _ _)
      (fun k => ⟨le_min (hlo k) (hhi k), min_le_left _ _⟩) (fun _ => le_rfl)
  have hLo : Tendsto (fun k => kthBidCDF k (V k) (E k) (lo k)) atTop (𝓝 0) := by
    apply hExt.2.2.1.congr'
    filter_upwards [hOrder] with k hk
    change kthBidCDF k (V k) (E k) (min (lo k) (hi k)) = _
    rw [min_eq_left hk]
  apply positive_utility_interval δ H n V E s hs c hc hOrder
    (Lemma3.solution δ hδ H κ hH hκ n V E hseq hA1 hA3 hA4 1 one_pos)
    hLo hExt.2.2.2 _ _ _ hwide
  · intro k d
    let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  · intro k i d
    let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
    exact ⟨alloc_nonneg k i d, alloc_le_one k i d⟩
  · intro k i d hd
    exact (Fact3.solution k (V k) (E k) (hseq.2.1 k) (hseq.2.2 k) d hd i).2 (hA4 k)

#print axioms solution
