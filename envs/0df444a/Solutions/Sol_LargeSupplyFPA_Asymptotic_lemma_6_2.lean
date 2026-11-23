-- Prove2me | solution 2 for LargeSupplyFPA.Asymptotic.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:29:18.217931+00:00
-- url     : https://prove2.me/submissions/08e44303-f40c-49ff-a4fa-9cc86c19b424

import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Extremizing
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Theorems.Thm_LargeSupplyFPA_Asymptotic_theorem_1
import Theorems.Thm_LargeSupplyFPA_Asymptotic_fact_3
import Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_1
import Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_3

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


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}

theorem utility_le_middle (k : ℕ) (i : Fin n) {v H l h u : ℝ} {μ : Measure ℝ}
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

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

namespace MultiUnitPoA

theorem monotone_kthBidCDF {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    [∀ j, IsProbabilityMeasure (marginalBid V E j)] : Monotone (kthBidCDF k V E) := by
  classical
  intro a b hab
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro β hβ
  change numAbove b β < k
  exact lt_of_le_of_lt (Finset.card_le_card (by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hab.trans_lt (Finset.mem_filter.mp hi).2⟩)) hβ

theorem cdf_area_bounds {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    [∀ j, IsProbabilityMeasure (marginalBid V E j)] {l h : ℝ} (hlh : l ≤ h) :
    0 ≤ (∫ b in l..h, kthBidCDF k V E b) ∧ (∫ b in l..h, kthBidCDF k V E b) ≤ h - l := by
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall hlh (fun _ => measureReal_nonneg)
  · have hInt : IntervalIntegrable (kthBidCDF k V E) volume l h :=
      (monotone_kthBidCDF k V E).intervalIntegrable
    simpa using intervalIntegral.integral_mono_on hlh hInt
      (intervalIntegrable_const (c := (1 : ℝ))) (fun _ _ => measureReal_le_one)


end MultiUnitPoA

open MeasureTheory ProbabilityTheory
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false


namespace Fact3

alias solution := _root_.LargeSupplyFPA.Asymptotic.fact_3


end Fact3

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

namespace MultiUnitPoA

theorem exists_small_middle_mass {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    {κ H a b lo hi τ : ℝ} (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    (hA1 : Assumption1 H κ V)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ H) (hτ : 0 ≤ τ)
    (hCount : (∑ i, (marginalBid V E i).real (Ioc lo hi)) <
      (n : ℝ) * (τ * (κ * (b - a)))) :
    ∃ i : Fin n, ∃ v ∈ Ioo a b, (E i v).real (Ioc lo hi) < τ := by
  by_contra! h
  have hEach (i : Fin n) : τ * (κ * (b - a)) ≤ (marginalBid V E i).real (Ioc lo hi) := by
    let := hV i
    let := (hE i).1
    have hM := (hA1 i).2 (b - a) (sub_pos.mpr hab) a ⟨ha, by linarith⟩
    have hEq : a + (b - a) = b := by ring
    rw [hEq] at hM
    exact (mul_le_mul_of_nonneg_left hM.le hτ).trans (marginalBid_middle_lower hτ (h i))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ => hEach i)
  exact (not_le_of_gt hCount) (by simpa using hs)

theorem area_bound_by_log {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    (k : ℕ) {d lo hi v H C : ℝ} (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    (hA4 : IsAtomless V E) (i : Fin n) (hlo : 0 ≤ lo) (hwide : lo ≤ hi - d)
    (hd : 0 < d) (hv : hi - d / 4 ≤ v) (hvH : v ≤ H) (hC : 0 ≤ C)
    (hUtil : ∀ b, 0 ≤ b → utility k V E i v b ≤ C) :
    (∫ b in lo..hi, kthBidCDF k V E b) ≤ C * Real.log (4 * H / (3 * d)) + d := by
  let : ∀ j, IsProbabilityMeasure (marginalBid V E j) := marginalBid_probability hV hE
  let F := kthBidCDF k V E
  let mid := hi - d
  have hm : lo ≤ mid := hwide
  have hmh : mid ≤ hi := sub_le_self _ hd.le
  have hp : 0 < v - mid := by dsimp [mid]; linarith
  have hpl : 0 < v - lo := by linarith
  have hiF₀ : IntervalIntegrable F volume lo mid := (monotone_kthBidCDF k V E).intervalIntegrable
  have hiF₁ : IntervalIntegrable F volume mid hi := (monotone_kthBidCDF k V E).intervalIntegrable
  have hiInv : IntervalIntegrable (fun b => C / (v - b)) volume lo mid := by
    refine ContinuousOn.intervalIntegrable ?_
    apply continuousOn_const.div (continuousOn_const.sub continuous_id.continuousOn)
    intro b hb
    rw [uIcc_of_le hm] at hb
    exact (show 0 < v - b by linarith [hb.2]).ne'
  have hPt (b : ℝ) (hb : b ∈ Icc lo mid) : F b ≤ C / (v - b) := by
    have hb0 := hlo.trans hb.1
    have hbv : 0 < v - b := by linarith [hb.2]
    have ha := (Fact3.solution k V E hV hE b hb0 i).2 hA4
    apply (le_div_iff₀ hbv).2
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left ha hbv.le).trans (hUtil b hb0)
  have hFirst := intervalIntegral.integral_mono_on hm hiF₀ hiInv hPt
  have hFormula : (∫ b in lo..mid, C / (v - b)) =
      C * Real.log ((v - lo) / (v - mid)) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) v, integral_inv_of_pos hp hpl, div_eq_mul_inv]
  rw [hFormula] at hFirst
  have hSecond := (cdf_area_bounds k V E hmh).2
  have hRatio : (v - lo) / (v - mid) ≤ 4 * H / (3 * d) := by
    have h3 : 0 < 3 * d / 4 := by positivity
    have hDen : 3 * d / 4 ≤ v - mid := by dsimp [mid]; linarith
    have hH : 0 < H := by linarith
    calc
      _ ≤ H / (v - mid) := div_le_div_of_nonneg_right (by linarith) hp.le
      _ ≤ H / (3 * d / 4) := div_le_div_of_nonneg_left hH.le h3 hDen
      _ = _ := by ring
  have hLog := Real.log_le_log (div_pos hpl hp) hRatio
  rw [← intervalIntegral.integral_add_adjacent_intervals hiF₀ hiF₁]
  change (∫ b in lo..mid, F b) + (∫ b in mid..hi, F b) ≤ _
  have hFirst' := hFirst.trans (mul_le_mul_of_nonneg_left hLog hC)
  change (∫ b in mid..hi, F b) ≤ hi - mid at hSecond
  dsimp [mid] at hSecond
  linarith

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA


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

private theorem tieShare_congr {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) {β γ : Fin n → ℝ}
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
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

namespace MultiUnitPoA

theorem ae_value_mem_Icc {n : ℕ} {V : Fin n → Measure ℝ} {H κ : ℝ}
    (hV : IsValueProfile V) (hA1 : Assumption1 H κ V) (i : Fin n) :
    ∀ᵐ v ∂V i, v ∈ Icc (0 : ℝ) H := by
  let := hV i
  exact (ae_mem_iff_measure_eq measurableSet_Icc.nullMeasurableSet).2
    ((hA1 i).1.trans (measure_univ (μ := V i)).symm)

theorem ae_value_profile {n : ℕ} {V : Fin n → Measure ℝ} {H κ : ℝ}
    (hV : IsValueProfile V) (hA1 : Assumption1 H κ V) :
    ∀ᵐ v ∂Measure.pi V, ∀ i, v i ∈ Icc (0 : ℝ) H := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  exact eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (μ := V)).eventually
    (ae_value_mem_Icc hV hA1 i))

theorem ae_pair_values {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ} {H κ : ℝ}
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hA1 : Assumption1 H κ V) :
    ∀ᵐ x ∂Measure.pi (pairLaw V E), ∀ i, (x i).1 ∈ Icc (0 : ℝ) H := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  let : ∀ i, IsMarkovKernel (E i) := fun i => (hE i).1
  let : ∀ i, IsProbabilityMeasure (pairLaw V E i) := pairLaw_probability hV hE
  apply eventually_all.mpr
  intro i
  have hv := ae_value_mem_Icc hV hA1 i
  rw [← pairLaw_map_fst V E i] at hv
  have hp : ∀ᵐ p ∂pairLaw V E i, p.1 ∈ Icc (0 : ℝ) H :=
    (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp hv
  exact (Measure.tendsto_eval_ae_ae (μ := pairLaw V E) (i := i)).eventually hp

theorem integrable_topKSum {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ} {H κ : ℝ}
    (hH : 0 ≤ H) (hV : IsValueProfile V) (hA1 : Assumption1 H κ V) :
    Integrable (topKSum k) (Measure.pi V) := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  apply (integrable_const ((k : ℝ) * H)).mono' (measurable_topKSum k).aestronglyMeasurable
  filter_upwards [ae_value_profile hV hA1] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (topKSum_nonneg k v)]
  exact topKSum_le k v hH (fun i => (hv i).2)

theorem welfare_eq_joint {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) {H κ : ℝ}
    (hA1 : Assumption1 H κ V) :
    welfare k V E = ∫ x, ∑ i, (x i).1 * tieShare k i (x i).2 (fun j => (x j).2)
      ∂Measure.pi (pairLaw V E) := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  let : ∀ i, IsMarkovKernel (E i) := fun i => (hE i).1
  let : ∀ i, IsProbabilityMeasure (pairLaw V E i) := pairLaw_probability hV hE
  let : ∀ i, IsProbabilityMeasure (marginalBid V E i) := marginalBid_probability hV hE
  have hIntegrable (i : Fin n) : Integrable
      (fun x : Fin n → ℝ × ℝ => (x i).1 * tieShare k i (x i).2 (fun j => (x j).2))
        (Measure.pi (pairLaw V E)) := by
    apply (integrable_const H).mono' _ _
    · exact ((measurable_fst.comp (measurable_pi_apply i)).mul
        ((measurable_tieShare_joint k i).comp
          ((measurable_snd.comp (measurable_pi_apply i)).prodMk measurable_snd_profile))).aestronglyMeasurable
    · filter_upwards [ae_pair_values hV hE hA1] with x hx
      have hx0 := (hx i).1
      have hxH := (hx i).2
      have ht0 := tieShare_nonneg k i (x i).2 (fun j => (x j).2)
      have ht1 := tieShare_le_one k i (x i).2 (fun j => (x j).2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 ht0)]
      exact (mul_le_of_le_one_right hx0 ht1).trans hxH
  rw [integral_finsetSum _ (fun i _ => hIntegrable i), welfare]
  apply Finset.sum_congr rfl
  intro i _
  rw [integrate_allocation k V E hV hE i Prod.fst (hIntegrable i)]
  have hPair : ∀ᵐ x ∂pairLaw V E i, x.1 ∈ Icc (0 : ℝ) H := by
    have hv := ae_value_mem_Icc hV hA1 i
    rw [← pairLaw_map_fst V E i] at hv
    exact (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp hv
  have hpInt : Integrable (fun p : ℝ × ℝ => p.1 * alloc k V E i p.2) (pairLaw V E i) := by
    apply (integrable_const H).mono'
      (measurable_fst.mul ((measurable_alloc k V E i).comp measurable_snd)).aestronglyMeasurable
    filter_upwards [hPair] with p hp
    change ‖p.1 * alloc k V E i p.2‖ ≤ H
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.1 (alloc_nonneg k i p.2))]
    exact (mul_le_of_le_one_right hp.1 (alloc_le_one k i p.2)).trans hp.2
  rw [pairLaw] at hpInt ⊢
  rw [Measure.integral_compProd hpInt]
  simp_rw [integral_const_mul]

theorem welfare_bounds {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (hk : k ≤ n) (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    {H κ : ℝ} (hH : 0 ≤ H) (hA1 : Assumption1 H κ V) :
    0 ≤ welfare k V E ∧ welfare k V E ≤ optWelfare k V := by
  rw [welfare_eq_joint k V E hV hE hA1]
  have hValues := ae_pair_values hV hE hA1
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hValues] with x hx
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx i).1 (tieShare_nonneg k i _ _))
  · unfold optWelfare
    let : ∀ i, IsProbabilityMeasure (V i) := hV
    let : ∀ i, IsProbabilityMeasure (pairLaw V E i) := pairLaw_probability hV hE
    have hm := pairProfile_map_fst V E hV hE
    rw [← hm, integral_map measurable_fst_profile.aemeasurable (measurable_topKSum k).aestronglyMeasurable]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [hValues] with x hx
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx i).1 (tieShare_nonneg k i _ _))
    · have hMP : MeasurePreserving (fun x : Fin n → ℝ × ℝ => fun i => (x i).1)
          (Measure.pi (pairLaw V E)) (Measure.pi V) := ⟨measurable_fst_profile, hm⟩
      exact hMP.integrable_comp_of_integrable (integrable_topKSum k hH hV hA1)
    · filter_upwards [hValues] with x hx
      have hsum := sum_tieShare k (fun j => (x j).2) hk
      exact fractional_le_topK k (fun j => (x j).1)
        (fun i => tieShare k i (x i).2 (fun j => (x j).2)) hk
        (fun i => (hx i).1) (fun i => ⟨tieShare_nonneg k i _ _,
          tieShare_le_one k i _ _⟩) hsum.le

theorem welfareRatio_bounds {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (hk : k ≤ n) (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    {H κ : ℝ} (hH : 0 ≤ H) (hA1 : Assumption1 H κ V) :
    0 ≤ welfareRatio k V E ∧ welfareRatio k V E ≤ 1 := by
  obtain ⟨h0, h1⟩ := welfare_bounds k V E hk hV hE hH hA1
  unfold welfareRatio
  rcases eq_or_lt_of_le (h0.trans h1) with hz | hp
  · simp [← hz]
  · exact ⟨div_nonneg h0 hp.le, (div_le_one hp).2 h1⟩

end MultiUnitPoA

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

alias solution := _root_.LargeSupplyFPA.Asymptotic.lemma_1


end Lemma1

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false


private theorem limit_of_middle_scale (δ : ℝ) (hδ : δ < (0.5 : ℝ)) :
    Tendsto (fun k : ℕ => 2 * (k : ℝ) ^ ((0.5 : ℝ) + δ) / k) atTop (𝓝 0) := by
  have hExp : 0 < 1 - ((0.5 : ℝ) + δ) := by linarith
  have h := (tendsto_const_nhds (x := (2 : ℝ))).mul
    ((tendsto_rpow_neg_atTop hExp).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hp : 0 < (k : ℝ) := by exact_mod_cast hk
  change 2 * (k : ℝ) ^ (-(1 - ((0.5 : ℝ) + δ))) = 2 * (k : ℝ) ^ ((0.5 : ℝ) + δ) / k
  have he : -(1 - ((0.5 : ℝ) + δ)) = ((0.5 : ℝ) + δ) - 1 := by ring
  rw [he, Real.rpow_sub_one hp.ne', ← mul_div_assoc]

private theorem liminf_from_subsequences (g : ℕ → ℝ) (L : ℝ)
    (h0 : ∀ k, 0 ≤ g k) (h1 : ∀ k, g k ≤ 1)
    (hsub : ∀ s : ℕ → ℕ, StrictMono s → ∃ θ : ℕ → ℕ, StrictMono θ ∧
      L ≤ liminf (g ∘ s ∘ θ) atTop) :
    L ≤ liminf g atTop := by
  by_contra! h
  let A := (L + liminf g atTop) / 2
  have hA : liminf g atTop < A := by dsimp [A]; linarith
  have hAL : A < L := by dsimp [A]; linarith
  have hex : ∃ᶠ k in atTop, g k < A := by
    by_contra! hn
    have hbounded : IsCoboundedUnder (· ≥ ·) atTop g := ⟨1, fun b hb => by
      obtain ⟨k, hk⟩ := (eventually_map.mp hb).exists
      exact hk.trans (h1 k)⟩
    exact hA.not_ge (le_liminf_of_le hbounded hn)
  obtain ⟨s, hs, hsA⟩ := extraction_of_frequently_atTop hex
  obtain ⟨θ, _, hθ⟩ := hsub s hs
  have hUp : liminf (g ∘ s ∘ θ) atTop ≤ A := by
    apply liminf_le_of_le (show IsBoundedUnder (· ≥ ·) atTop (g ∘ s ∘ θ) from
      isBoundedUnder_of ⟨0, fun k => h0 (s (θ k))⟩)
    intro b hb
    obtain ⟨k, hk⟩ := hb.exists
    exact hk.trans (hsA (θ k)).le
  exact hAL.not_ge (hθ.trans hUp)

theorem solution (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ) :
    ∃ ζ' : ℝ, 0 < ζ' ∧
      ∀ (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
        (εs : ℕ → ℝ) (εstar : ℝ),
        IsAuctionSequence n V E →
        (∀ k, Assumption1 H κ (V k)) →
        (∀ k, IsApproxBNE k (V k) (E k) (εs k)) →
        Assumption3 n V E →
        (∀ k, IsAtomless (V k) (E k)) →
        Tendsto εs atTop (𝓝 εstar) →
        εstar ∈ Ioo 0 H →
        1 - ζ' * εstar * (1 + Real.log (H / εstar)) ≤
          Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop := by
  obtain ⟨ζ, hζ, hW⟩ := theorem_1 H κ hH hκ
  let ζ' := (3 : ℝ) / ζ
  refine ⟨ζ', by positivity, ?_⟩
  intro n V E εs d hSeq hA1 hBNE hA3 hA4 hε hd
  have hd0 : 0 < d := hd.1
  let δ : ℝ := 1 / 4
  have hδ : δ ∈ Ioo (0 : ℝ) 0.5 := by constructor <;> norm_num [δ]
  let lo₀ (k : ℕ) := lowThreshold δ k (V k) (E k)
  let hi (k : ℕ) := highThreshold δ k (V k) (E k)
  let lo (k : ℕ) := min (lo₀ k) (hi k)
  let g (k : ℕ) := welfareRatio k (V k) (E k)
  let c := d * Real.log (4 * H / (3 * d)) + d
  let B := 1 - ζ' * d * (1 + Real.log (H / d))
  have hLog : 0 ≤ Real.log (4 * H / (3 * d)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by positivity)).2
    linarith [hd.2]
  have hc : 0 ≤ c := add_nonneg (mul_nonneg hd.1.le hLog) hd.1.le
  have hConst : B ≤ 1 - c / ζ - d / ζ := by
    have hEq : 4 * H / (3 * d) = (4 / 3 : ℝ) * (H / d) := by ring
    have hHratio : 0 < H / d := div_pos hH hd.1
    have hlog1 : 0 ≤ Real.log (H / d) :=
      Real.log_nonneg ((le_div_iff₀ hd.1).2 (by simpa using hd.2.le))
    have hlog2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    have hN : c + d ≤ 3 * d * (1 + Real.log (H / d)) := by
      dsimp [c]
      rw [hEq, Real.log_mul (by norm_num) hHratio.ne']
      nlinarith [mul_le_mul_of_nonneg_left hlog2 hd.1.le, mul_nonneg hd.1.le hlog1]
    dsimp [B, ζ']
    have hD := div_le_div_of_nonneg_right hN hζ.le
    calc
      _ = 1 - (3 * d * (1 + Real.log (H / d))) / ζ := by ring
      _ ≤ 1 - (c + d) / ζ := sub_le_sub_left hD 1
      _ = _ := by ring
  have hR (k : ℕ) := welfareRatio_bounds k (V k) (E k) (hSeq.1 k).le
    (hSeq.2.1 k) (hSeq.2.2 k) hH.le (hA1 k)
  apply liminf_from_subsequences g B (fun k => (hR k).1) (fun k => (hR k).2)
  intro s hs
  have hOrd : ∀ᶠ k in atTop, lo k = lo₀ k := by
    filter_upwards [eventually_threshold_scale δ hδ] with k hk
    apply min_eq_left
    apply lowThreshold_le_highThreshold
    let : ∀ i, IsProbabilityMeasure (marginalBid (V k) (E k) i) :=
      marginalBid_probability (hSeq.2.1 k) (hSeq.2.2 k)
    have hT : ∀ᶠ b : ℝ in atTop, expNumAbove (V k) (E k) b <
        (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1 :=
      Tendsto.eventually tendsto_expNumAbove (eventually_lt_nhds hk.2.2)
    obtain ⟨x, hx, hx0⟩ := (hT.and (eventually_ge_atTop (0 : ℝ))).exists
    exact ⟨x, hx0, hx.le⟩
  have hExt : IsExtremizing n V E lo hi id :=
    Lemma1.solution δ hδ n V E hSeq hA4 lo hi (fun k => min_le_right _ _)
      (fun k => ⟨le_min threshold_nonneg threshold_nonneg, min_le_left _ _⟩) (fun _ => le_rfl)
  have hUpper := Lemma3.solution δ hδ H κ hH hκ n V E hSeq hA1 hA3 hA4 (d / 32) (by positivity)
  let A (k : ℕ) := ∫ b in lo k..hi k, kthBidCDF k (V k) (E k) b
  have hArea (k : ℕ) := by
    let : ∀ i, IsProbabilityMeasure (marginalBid (V k) (E k) i) :=
      marginalBid_probability (hSeq.2.1 k) (hSeq.2.2 k)
    exact cdf_area_bounds k (V k) (E k) (min_le_right _ _ : lo k ≤ hi k)
  have hEventuallyBound : ∀ᶠ k in atTop, A k ∈ Icc (0 : ℝ) (H + d / 32) := by
    filter_upwards [hUpper] with k hk
    exact ⟨(hArea k).1, ((hArea k).2.trans (sub_le_self _ (hExt.2.1 k).1)).trans hk⟩
  obtain ⟨L, _, θ, hθ, hLim⟩ := isCompact_Icc.tendsto_subseq'
    (x := A ∘ s) (hs.tendsto_atTop.eventually hEventuallyBound).frequently
  have hL : L ≤ c := by
    let φ := s ∘ θ
    by_contra! hLc
    let r := (L - c) / 2
    have hr : 0 < r := by dsimp [r]; linarith
    let Q := Real.log (4 * H / (3 * d))
    let τ := r / (4 * H * (Q + 1))
    have hτ : 0 < τ := by dsimp [τ, Q]; positivity
    have hτQ : H * τ * Q ≤ r / 4 := by
      dsimp [τ]
      have hD : 0 < 4 * H * (Q + 1) := by dsimp [Q]; positivity
      have hEq : H * (r / (4 * H * (Q + 1))) * Q = (H * r * Q) / (4 * H * (Q + 1)) := by
        ring
      rw [hEq]
      apply (div_le_iff₀ hD).2
      have hNonneg : 0 ≤ H * r := mul_nonneg hH.le hr.le
      nlinarith
    have hφ := (hs.comp hθ).tendsto_atTop
    let err (k : ℕ) := 8 * k / ((k : ℝ) ^ ((0.5 : ℝ) + δ)) ^ 2
    have hC : Tendsto (fun k => (H * err k + εs k) * Q + d) atTop (𝓝 c) := by
      have h := (((tendsto_const_nhds (x := H)).mul (tendsto_tail_error δ hδ.1)).add hε).mul_const Q
      simpa only [mul_zero, zero_add] using h.add_const d
    have hGood : ∀ᶠ k : ℕ in atTop, 2 * (k : ℝ) ^ ((0.5 : ℝ) + δ) / k < τ * (κ * (d / 8)) :=
      (limit_of_middle_scale δ hδ.2).eventually
        (eventually_lt_nhds (by positivity : 0 < τ * (κ * (d / 8))))
    have hFalse : ∀ᶠ _m : ℕ in atTop, False := by
      filter_upwards [hLim.eventually (eventually_gt_nhds (show c + r < L by dsimp [r]; linarith)),
        hφ.eventually hOrd, hφ.eventually hUpper, hφ.eventually hGood,
        hφ.eventually (eventually_threshold_scale δ hδ), hφ.eventually (eventually_gt_atTop (0 : ℕ)),
        hφ.eventually (hC.eventually (eventually_le_nhds (show c < c + r / 2 by linarith)))]
        with m hm hOrder hHi hN hScale hk hEps
      let k := φ m
      let a := hi k - d / 4
      let b := hi k - d / 8
      have hgap : d < hi k - lo k := by
        have h := (hArea k).2
        change c + r < A k at hm
        dsimp only [A] at hm
        dsimp only [c] at hm
        linarith [mul_nonneg hd.1.le hLog]
      have hlo : 0 ≤ lo k := (hExt.2.1 k).1
      have ha : 0 ≤ a := by dsimp [a]; linarith
      have hab : a < b := by dsimp [a, b]; linarith [hd.1]
      change hi k ≤ H + d / 32 at hHi
      have hb : b ≤ H := by dsimp [b]; linarith
      let : ∀ i, IsProbabilityMeasure (marginalBid (V k) (E k) i) :=
        marginalBid_probability (hSeq.2.1 k) (hSeq.2.2 k)
      have hCount := middle_bid_count_le δ k (hSeq.1 k) (hSeq.2.2 k) (hA4 k) hScale.2.2
      have hLen : b - a = d / 8 := by dsimp [a, b]; ring
      have hCut : (∑ i, (marginalBid (V k) (E k) i).real (Ioc (lo k) (hi k))) <
          (n k : ℝ) * (τ * (κ * (b - a))) := by
        have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
        have hkn : (k : ℝ) ≤ n k := by exact_mod_cast (hSeq.1 k).le
        rw [hLen, hOrder]
        change 2 * (k : ℝ) ^ ((0.5 : ℝ) + δ) / k < τ * (κ * (d / 8)) at hN
        have hn := (div_lt_iff₀ hkp).1 hN
        apply hCount.trans_lt
        exact (by simpa only [mul_comm] using hn : _ < (k : ℝ) * (τ * (κ * (d / 8)))).trans_le
          (mul_le_mul_of_nonneg_right hkn (by positivity))
      obtain ⟨i, v, hv, hMass⟩ := exists_small_middle_mass
        (hSeq.2.1 k) (hSeq.2.2 k) (hA1 k) ha hab hb hτ.le hCut
      have hvH : v ≤ H := hv.2.le.trans hb
      have hvHi : v ≤ hi k := hv.2.le.trans (sub_le_self _ (by positivity))
      have hvSupp := density_support hκ (hA1 k) i ⟨ha.trans_lt hv.1, hv.2.trans_le hb⟩
      let := (hSeq.2.2 k i).1
      have hNonneg : ∀ᵐ b ∂E k i v, 0 ≤ b := by
        rw [ae_iff]
        simpa only [not_le, Set.Iio] using (hSeq.2.2 k i).2 v
      obtain ⟨hUi, hDev⟩ := hBNE k i v hvSupp
      have hPay := utility_le_middle k i hvH hvHi hH.le (show 0 ≤ err k by dsimp [err]; positivity) hNonneg hUi
        (alloc_nonneg k i) (alloc_le_one k i) (l := lo k)
        (fun bid hb₀ hbLo => alloc_low_bound δ k (hSeq.1 k) (hSeq.2.2 k) (hA4 k) i bid
          ⟨hb₀, hbLo.trans (min_le_left _ _)⟩ hScale.1 hScale.2.1)
      change (∫ bid, utility k (V k) (E k) i v bid ∂E k i v) ≤
        H * err k + H * ((E k i) v).real (Ioc (lo k) (hi k)) at hPay
      let C := H * err k + H * τ + εs k
      have hC₀ : 0 ≤ C := by
        have hZero := hDev 0 le_rfl
        have hp := mul_nonneg (ha.trans hv.1.le) (alloc_nonneg (V := V k) (E := E k) k i 0)
        change (v - 0) * alloc k (V k) (E k) i 0 - εs k ≤ _ at hZero
        rw [sub_zero] at hZero
        dsimp [C]
        linarith [mul_le_mul_of_nonneg_left hMass.le hH.le]
      have hDb (bid : ℝ) (hb0 : 0 ≤ bid) : utility k (V k) (E k) i v bid ≤ C := by
        dsimp [C]
        linarith [hDev bid hb0, mul_le_mul_of_nonneg_left hMass.le hH.le]
      have hBound := area_bound_by_log k (hSeq.2.1 k) (hSeq.2.2 k) (hA4 k) i (hExt.2.1 k).1
        (show lo k ≤ hi k - d by linarith) hd.1 hv.1.le hvH hC₀ hDb
      change A k ≤ C * Q + d at hBound
      change (H * err k + εs k) * Q + d ≤ c + r / 2 at hEps
      change c + r < A k at hm
      dsimp [C] at hBound
      nlinarith [hτQ]
    exact hFalse.exists.choose_spec
  refine ⟨θ, hθ, hConst.trans ?_⟩
  exact hW n V E εs d hSeq hA1 hBNE hA3 hε c hc lo hi (s ∘ θ)
    ⟨hs.comp hθ, hExt.2.1, hExt.2.2.1.comp (hs.comp hθ).tendsto_atTop,
      hExt.2.2.2.comp (hs.comp hθ).tendsto_atTop⟩ ⟨L, hLim, hL⟩

#print axioms solution
