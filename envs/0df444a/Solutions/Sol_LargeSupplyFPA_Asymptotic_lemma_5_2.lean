-- Prove2me | solution 2 for LargeSupplyFPA.Asymptotic.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:29:17.542063+00:00
-- url     : https://prove2.me/submissions/f7ef993e-53a1-4c19-876c-6f1b1309e918

import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_3
import Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_4

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


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable [∀ j, IsProbabilityMeasure (marginalBid V E j)]


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


end MultiUnitPoA

open MeasureTheory ProbabilityTheory
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false


namespace Fact3


end Fact3

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false


namespace Lemma3

alias solution := _root_.LargeSupplyFPA.Asymptotic.lemma_3


end Lemma3

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Lemma1


end Lemma1

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}

private theorem threshold_count_eq {f : ℝ → ℝ} (hc : Continuous f)
    (hf : Tendsto f atTop (𝓝 0)) {q : ℝ} (hq : 0 < q)
    (h0 : q < f 0) :
    f (sInf {b : ℝ | 0 ≤ b ∧ f b ≤ q}) = q := by
  let t := sInf {b : ℝ | 0 ≤ b ∧ f b ≤ q}
  have ht : 0 ≤ t ∧ f t ≤ q := threshold_mem hc hf hq
  have htp : 0 < t := by
    by_contra! h
    have htz : t = 0 := le_antisymm h ht.1
    exact (not_lt_of_ge (htz ▸ ht.2)) h0
  apply le_antisymm ht.2
  by_contra! hlt
  have hOpen : IsOpen {x | 0 < x ∧ f x < q} :=
    isOpen_Ioi.inter (isOpen_lt hc continuous_const)
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hOpen t ⟨htp, hlt⟩
  have hball : t - ε / 2 ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have : t - ε / 2 - t = -(ε / 2) := by ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
    linarith
  have hx := hsub hball
  have hle : t ≤ t - ε / 2 := csInf_le ⟨0, fun _ hy => hy.1⟩ ⟨hx.1.le, hx.2.le⟩
  linarith

theorem expNumAbove_zero [∀ j, IsProbabilityMeasure (marginalBid V E j)]
    (hE : IsStrategyProfile E) (hA4 : IsAtomless V E) : expNumAbove V E 0 = (n : ℝ) := by
  unfold expNumAbove
  have h (i : Fin n) : (marginalBid V E i).real (Ioi 0) = 1 := by
    have hU : Set.Iio (0 : ℝ) ∪ {0} = Set.Iic 0 := by
      ext x
      simp [le_iff_lt_or_eq]
    have hz : marginalBid V E i (Iic 0) = 0 := by
      rw [← hU, measure_union_null (marginalBid_negative_zero (V := V) hE i) (hA4 i 0)]
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, Measure.real, hz]
    simp
  simp [h]

theorem middle_bid_count_le [∀ j, IsProbabilityMeasure (marginalBid V E j)]
    (δ : ℝ) (k : ℕ) (hkn : k < n) (hE : IsStrategyProfile E) (hA4 : IsAtomless V E)
    (hHigh : 0 < (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1) :
    (∑ i : Fin n, (marginalBid V E i).real (Ioc (lowThreshold δ k V E) (highThreshold δ k V E))) ≤
      2 * (k : ℝ) ^ ((0.5 : ℝ) + δ) := by
  have hr : (k : ℝ) < n := by exact_mod_cast hkn
  have hpow : 0 ≤ (k : ℝ) ^ ((0.5 : ℝ) + δ) := by positivity
  have hhi : expNumAbove V E (highThreshold δ k V E) =
      (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 := by
    apply threshold_count_eq (continuous_expNumAbove hA4) tendsto_expNumAbove hHigh
    rw [expNumAbove_zero hE hA4]
    linarith
  have hlo : expNumAbove V E (lowThreshold δ k V E) ≤
      (k : ℝ) + (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 :=
    (threshold_mem (continuous_expNumAbove hA4) tendsto_expNumAbove (by linarith)).2
  have hord : lowThreshold δ k V E ≤ highThreshold δ k V E := by
    apply csInf_le ⟨0, fun _ hb => hb.1⟩
    exact ⟨Real.sInf_nonneg (fun _ hb => hb.1), by linarith⟩
  have hdiff (i : Fin n) :
      (marginalBid V E i).real (Ioc (lowThreshold δ k V E) (highThreshold δ k V E)) =
        (marginalBid V E i).real (Ioi (lowThreshold δ k V E)) -
          (marginalBid V E i).real (Ioi (highThreshold δ k V E)) := by
    rw [← Ioi_sdiff_Ioi]
    exact measureReal_sdiff (Ioi_subset_Ioi hord) measurableSet_Ioi
  simp_rw [hdiff]
  rw [Finset.sum_sub_distrib]
  change expNumAbove V E (lowThreshold δ k V E) -
    expNumAbove V E (highThreshold δ k V E) ≤ _
  linarith

theorem marginalBid_middle_lower {i : Fin n} [IsMarkovKernel (E i)]
    [IsProbabilityMeasure (V i)] {a b l h τ : ℝ} (hτ : 0 ≤ τ)
    (hmass : ∀ v ∈ Ioo a b, τ ≤ (E i v).real (Ioc l h)) :
    τ * (V i).real (Ioo a b) ≤ (marginalBid V E i).real (Ioc l h) := by
  classical
  let hprob : IsProbabilityMeasure (marginalBid V E i) :=
    isProbabilityMeasure_bind (E i).aemeasurable
    (Filter.Eventually.of_forall fun _ => inferInstance)
  have hbound : ∀ v, (Ioo a b).indicator (fun _ => ENNReal.ofReal τ) v ≤ E i v (Ioc l h) := by
    intro v
    by_cases hv : v ∈ Ioo a b
    · rw [Set.indicator_of_mem hv]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (hmass v hv)
    · simp [Set.indicator_of_notMem hv]
  have hi := lintegral_mono (μ := V i) hbound
  rw [lintegral_indicator_const measurableSet_Ioo, ← Measure.bind_apply measurableSet_Ioc
    (E i).aemeasurable] at hi
  have hfin : marginalBid V E i (Ioc l h) ≠ ∞ := measure_ne_top _ _
  simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ, marginalBid] using
    ENNReal.toReal_mono hfin hi

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}

private theorem utility_le_middle (k : ℕ) (i : Fin n) {v H l h u : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hvH : v ≤ H) (hvh : v ≤ h) (hH : 0 ≤ H) (hu : 0 ≤ u)
    (hNonnegative : ∀ᵐ b ∂μ, 0 ≤ b) (hInt : Integrable (utility k V E i v) μ)
    (hAlloc0 : ∀ b, 0 ≤ alloc k V E i b)
    (hAlloc1 : ∀ b, alloc k V E i b ≤ 1)
    (hAllocLow : ∀ b, 0 ≤ b → b ≤ l → alloc k V E i b ≤ u) :
    (∫ b, utility k V E i v b ∂μ) ≤ H * u + H * μ.real (Ioc l h) := by
  let f := (Ioc l h).indicator (fun _ : ℝ => H)
  have hf : Integrable f μ := (integrable_const H).indicator measurableSet_Ioc
  calc
    _ ≤ ∫ b, H * u + f b ∂μ := by
      apply integral_mono_ae hInt ((integrable_const (H * u)).add hf)
      filter_upwards [hNonnegative] with b hb
      have hbase : 0 ≤ H * u := mul_nonneg hH hu
      change (v - b) * alloc k V E i b ≤ H * u + f b
      by_cases hlow : b ≤ l
      · have hh : b ∉ Ioc l h := fun hb' => (not_lt_of_ge hlow) hb'.1
        rw [show f b = 0 from indicator_of_notMem hh _]
        rw [add_zero]
        exact (mul_le_mul_of_nonneg_right (show v - b ≤ H by linarith) (hAlloc0 b)).trans
          (mul_le_mul_of_nonneg_left (hAllocLow b hb hlow) hH)
      · by_cases hhigh : b ≤ h
        · have hh : b ∈ Ioc l h := ⟨lt_of_not_ge hlow, hhigh⟩
          rw [show f b = H from indicator_of_mem hh _]
          exact ((mul_le_mul_of_nonneg_right (show v - b ≤ H by linarith) (hAlloc0 b)).trans
            (by simpa using mul_le_mul_of_nonneg_left (hAlloc1 b) hH)).trans (by linarith)
        · have hh : b ∉ Ioc l h := fun hb' => hhigh hb'.2
          rw [show f b = 0 from indicator_of_notMem hh _, add_zero]
          exact (mul_nonpos_of_nonpos_of_nonneg (by linarith [lt_of_not_ge hhigh]) (hAlloc0 b)).trans hbase
    _ = _ := by
      rw [integral_add (integrable_const (H * u)) hf, integral_const, probReal_univ, one_smul]
      unfold f
      rw [integral_indicator_const H measurableSet_Ioc, smul_eq_mul, mul_comm (μ.real (Ioc l h)) H]

theorem conditional_middle_mass [∀ j, IsProbabilityMeasure (marginalBid V E j)]
    (k : ℕ) (i : Fin n) {ε H l h ubar e v : ℝ}
    (hStrategy : IsStrategyProfile E) (hBNE : IsApproxBNE k V E ε)
    (hv : v ∈ (V i).support) (hvH : v ≤ H) (hvh : v ≤ h)
    (hH : 0 < H) (he : 0 ≤ e)
    (hLow : ∀ b, 0 ≤ b → b ≤ l → alloc k V E i b ≤ e)
    (hOpt : ubar ≤ optUtility k V E i v)
    (hε : ε ≤ ubar / 4) (heH : H * e ≤ ubar / 4) :
    ubar / (2 * H) ≤ (E i v).real (Ioc l h) := by
  let hMarkov := (hStrategy i).1
  have hBid : ∀ᵐ b ∂E i v, 0 ≤ b := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using (hStrategy i).2 v
  obtain ⟨hint, hdev⟩ := hBNE i v hv
  have hExp := utility_le_middle k i hvH hvh hH.le he hBid hint
    (alloc_nonneg k i) (alloc_le_one k i) hLow
  have hbest : optUtility k V E i v ≤ (∫ b, utility k V E i v b ∂E i v) + ε := by
    unfold optUtility
    exact ciSup_le fun b => by linarith [hdev b.val b.property]
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem density_support {H κ : ℝ} (hκ : 0 < κ) (hA1 : Assumption1 H κ V)
    (i : Fin n) {v : ℝ} (hv : v ∈ Ioo 0 H) : v ∈ (V i).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let Δ := min r (H - v)
  have hd0 : 0 < Δ := lt_min hr (sub_pos.mpr hv.2)
  have hdH : Δ ≤ H - v := min_le_right _ _
  have hmass := (hA1 i).2 Δ hd0 v ⟨hv.1.le, by linarith⟩
  have hsub : Ioo v (v + Δ) ⊆ U := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hx.1)]
    have hdR : Δ ≤ r := min_le_left _ _
    linarith [hx.2]
  exact lt_of_lt_of_le
    (ENNReal.toReal_pos_iff.mp (lt_trans (mul_pos hκ hd0) hmass)).1
    (measure_mono hsub)

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Lemma4

alias solution := _root_.LargeSupplyFPA.Asymptotic.lemma_4


end Lemma4

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic MultiUnitPoA
open scoped BigOperators

set_option autoImplicit false


private theorem threshold_scale_ratio (δ : ℝ) (hδ : δ < (0.5 : ℝ)) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ ((0.5 : ℝ) + δ) / k) atTop (𝓝 0) := by
  have hExp : 0 < 1 - ((0.5 : ℝ) + δ) := by linarith
  have h := (tendsto_rpow_neg_atTop hExp).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hp : 0 < (k : ℝ) := by exact_mod_cast hk
  change (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) =
    (k : ℝ) ^ ((0.5 : ℝ) + δ) / k
  have he : -(1 - ((0.5 : ℝ) + δ)) = ((0.5 : ℝ) + δ) - 1 := by ring
  rw [he, Real.rpow_sub_one hp.ne']

theorem solution (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (εs : ℕ → ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hBNE : ∀ k, IsApproxBNE k (V k) (E k) (εs k))
    (hA3 : Assumption3 n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (hε : Tendsto εs atTop (𝓝 0)) :
    ∀ s : ℕ → ℕ, StrictMono s → ∀ c : ℝ, 0 < c →
      ∃ (lo hi : ℕ → ℝ) (θ : ℕ → ℕ), StrictMono θ ∧ IsExtremizing n V E lo hi (s ∘ θ) ∧
        ∃ L : ℝ, Tendsto (fun l => hi (s (θ l)) - lo (s (θ l))) atTop (𝓝 L) ∧ L < c := by
  intro s hs c hc
  by_contra! hfail
  let δ : ℝ := 1 / 4
  have hδ : δ ∈ Ioo (0 : ℝ) 0.5 := by
    constructor <;> norm_num [δ]
  have hwide (lo hi : ℕ → ℝ) (θ : ℕ → ℕ) (hθ : StrictMono θ)
      (hext : IsExtremizing n V E lo hi (s ∘ θ))
      (L : ℝ) (hL : Tendsto (fun l => hi (s (θ l)) - lo (s (θ l))) atTop (𝓝 L)) :
      c / 2 < L := (by linarith : c / 2 < c).trans_le (hfail lo hi θ hθ hext L hL)
  obtain ⟨ubar, hu, θ, hθ, mstar, hinterval⟩ :=
    Lemma4.solution δ hδ H κ hH hκ n V E hseq hA1 hA3 hA4 s hs (c / 2) (by positivity) hwide
  let τ : ℝ := ubar / (2 * H)
  let q : ℝ := τ * (κ * (c / 32))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  let error : ℕ → ℝ := fun k => 8 * k / ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2
  have hError : ∀ᶠ k in atTop, H * error k ≤ ubar / 4 := by
    have h : Tendsto (fun k => H * error k) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (x := H)).mul (tendsto_tail_error δ hδ.1)
    exact h.eventually (eventually_le_nhds (show 0 < ubar / 4 by positivity))
  have hSmall : ∀ᶠ k : ℕ in atTop, 2 * ((k : ℝ) ^ ((0.5 : ℝ) + δ) / k) < q := by
    have h : Tendsto (fun k : ℕ => 2 * ((k : ℝ) ^ ((0.5 : ℝ) + δ) / k)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (x := (2 : ℝ))).mul (threshold_scale_ratio δ hδ.2)
    exact h.eventually (eventually_lt_nhds hq)
  have hHi := Lemma3.solution δ hδ H κ hH hκ n V E hseq hA1 hA3 hA4
    (c / 32) (by positivity)
  have hApprox := hε.eventually (eventually_le_nhds (show 0 < ubar / 4 by positivity))
  have hφ : Tendsto (s ∘ θ) atTop atTop := (hs.comp hθ).tendsto_atTop
  have hAll : ∀ᶠ _m : ℕ in atTop, False := by
    filter_upwards [eventually_gt_atTop mstar, hφ.eventually hHi, hφ.eventually hApprox,
      hφ.eventually hError, hφ.eventually hSmall, hφ.eventually (eventually_threshold_scale δ hδ),
      hφ.eventually (eventually_gt_atTop (0 : ℕ))] with m hm hHi' hApprox' hError' hSmall' hScale hkpos
    let k := s (θ m)
    let lo := lowThreshold δ k (V k) (E k)
    let hi := highThreshold δ k (V k) (E k)
    let (i : Fin (n k)) := marginalBid_probability (hseq.2.1 k) (hseq.2.2 k) i
    obtain ⟨a, b, ha, hab, hb, huopt⟩ := hinterval m hm
    have ha0 : 0 ≤ a := le_of_lt ((show 0 ≤ lo from threshold_nonneg).trans_lt ha)
    have hab' : a + c / 32 ≤ b := by linarith
    have haH : a + c / 32 ≤ H := by
      change hi ≤ H + c / 32 at hHi'
      change b < hi at hb
      linarith
    have hmass (i : Fin (n k)) :
        κ * (c / 32) < (V k i).real (Ioo a (a + c / 32)) :=
      (hA1 k i).2 (c / 32) (by positivity) a ⟨ha0, by linarith⟩
    have hMarginal (i : Fin (n k)) :
        q ≤ (marginalBid (V k) (E k) i).real (Ioc lo hi) := by
      let hv := hseq.2.1 k i
      let he := (hseq.2.2 k i).1
      refine (mul_le_mul_of_nonneg_left (hmass i).le hτ.le).trans
        (marginalBid_middle_lower hτ.le ?_)
      intro v hvab
      have hvH : v ≤ H := (hvab.2.trans_le haH).le
      have hvhi : v ≤ hi := ((hvab.2.trans_le hab').trans hb).le
      have hvs : v ∈ (V k i).support :=
        density_support hκ (hA1 k) i ⟨ha0.trans_lt hvab.1, hvab.2.trans_le haH⟩
      exact conditional_middle_mass k i (hseq.2.2 k) (hBNE k) hvs hvH hvhi hH
        (by positivity)
        (fun d h0 hd => alloc_low_bound δ k (hseq.1 k) (hseq.2.2 k) (hA4 k) i d
          ⟨h0, hd⟩ hScale.1 hScale.2.1)
        (huopt i v ⟨hvab.1.le, hvab.2.le.trans hab'⟩) hApprox' hError'
    have hLower : (n k : ℝ) * q ≤
        ∑ i : Fin (n k), (marginalBid (V k) (E k) i).real (Ioc lo hi) := by
      simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n k))))
        (fun i _ => hMarginal i)
    have hUpper := middle_bid_count_le δ k (hseq.1 k) (hseq.2.2 k) (hA4 k) hScale.2.2
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hkn : (k : ℝ) ≤ n k := by exact_mod_cast (hseq.1 k).le
    change 2 * ((k : ℝ) ^ ((0.5 : ℝ) + δ) / k) < q at hSmall'
    rw [← mul_div_assoc, div_lt_iff₀ hkR] at hSmall'
    have hLower' := (mul_le_mul_of_nonneg_right hkn hq.le).trans hLower
    exact (not_lt_of_ge (hLower'.trans hUpper)) (by simpa [mul_comm] using hSmall')
  exact hAll.exists.choose_spec

#print axioms solution
