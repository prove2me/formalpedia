-- Prove2me | solution 2 for LargeSupplyFPA.Asymptotic.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T15:32:59.960238+00:00
-- url     : https://prove2.me/submissions/80da38cd-a1d0-4074-bfed-91d07e2a3a21

import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Smoothing
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
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

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic
open scoped ENNReal ProbabilityTheory

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable {ω : ℝ} {s : ℝ → ℝ}

theorem countable_atomSet [∀ i, IsProbabilityMeasure (marginalBid V E i)] :
    (atomSet V E).Countable := by
  have he : atomSet V E = ⋃ i, {p | 0 < marginalBid V E i {p}} := by
    ext p
    simp [atomSet, pos_iff_ne_zero]
  rw [he]
  apply countable_iUnion
  intro i
  apply Measure.countable_meas_pos_of_disjoint_iUnion (As := fun p : ℝ => {p})
    (fun p => measurableSet_singleton p)
  intro p q hpq
  exact disjoint_singleton_left.mpr (by simpa using hpq)

theorem exists_smoothingWeights [∀ i, IsProbabilityMeasure (marginalBid V E i)] (hω : 0 < ω) :
    ∃ s, IsSmoothingWeights V E ω s := by
  classical
  let : Countable (atomSet V E) := countable_atomSet (V := V) (E := E)
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat (atomSet V E)
  let g (j : ℕ) := ω / 2 / 2 / (2 : ℝ) ^ j
  let s (p : ℝ) := if hp : p ∈ atomSet V E then g (f ⟨p, hp⟩) else 0
  have he (p : atomSet V E) : s p = g (f p) := dif_pos p.property
  have hg : Summable g := summable_geometric_two' (ω / 2)
  have hs : Summable fun p : atomSet V E => s p := by
    simp_rw [he]
    apply summable_of_sum_le (c := ω / 2)
    · intro p
      dsimp [g]
      positivity
    · intro T
      rw [← Finset.sum_image hf.injOn]
      exact (hg.sum_le_tsum (T.image f) (fun _ _ => by dsimp [g]; positivity)).trans_eq
        (tsum_geometric_two' (ω / 2))
  refine ⟨s, fun p hp => ?_, hs, ?_⟩
  · rw [he ⟨p, hp⟩]
    dsimp [g]
    positivity
  · refine lt_of_le_of_lt (hs.tsum_le_of_sum_le (a₂ := ω / 2) fun T => ?_) (by linarith)
    simp_rw [he]
    rw [← Finset.sum_image hf.injOn]
    exact (hg.sum_le_tsum (T.image f) (fun _ _ => by dsimp [g]; positivity)).trans_eq
      (tsum_geometric_two' (ω / 2))

theorem atomShift_nonneg (hs : IsSmoothingWeights V E ω s) (b : ℝ) :
    0 ≤ atomShift V E s b := tsum_nonneg fun p => (hs.1 p p.property.1).le

private theorem atomWeight_sum_bound (hs : IsSmoothingWeights V E ω s)
    (A B : Set ℝ) (hA : A ⊆ atomSet V E) (hB : B ⊆ atomSet V E) (hab : A ⊆ B) :
    Summable (fun p : A => s p) ∧ (∑' p : A, s p) ≤ ∑' p : B, s p := by
  classical
  have hS (U : Set ℝ) (hU : U ⊆ atomSet V E) : Summable (fun p : U => s p) := by
    let f (p : U) : atomSet V E := ⟨p, hU p.property⟩
    have hf : Function.Injective f := fun p q he => Subtype.ext (congrArg (fun (p : atomSet V E) => (p : ℝ)) he)
    apply summable_of_sum_le (c := ∑' p : atomSet V E, s p) (fun p : U => (hs.1 p (hU p.property)).le)
    intro T
    have he : (∑ p ∈ T, s p) = ∑ p ∈ T.image f, s p := by
      rw [Finset.sum_image hf.injOn]
    exact he.trans_le (hs.2.1.sum_le_tsum _ (fun p _ => (hs.1 p p.property).le))
  refine ⟨hS A hA, ?_⟩
  let f (p : A) : B := ⟨p, hab p.property⟩
  have hf : Function.Injective f := fun p q he => Subtype.ext (congrArg (fun (p : B) => (p : ℝ)) he)
  apply (hS A hA).tsum_le_of_sum_le
  intro T
  have he : (∑ p ∈ T, s p) = ∑ p ∈ T.image f, s p := by rw [Finset.sum_image hf.injOn]
  exact he.trans_le ((hS B hB).sum_le_tsum _ (fun p _ => (hs.1 p (hB p.property)).le))

theorem monotone_atomShift (hs : IsSmoothingWeights V E ω s) : Monotone (atomShift V E s) := by
  intro a b h
  exact (atomWeight_sum_bound hs {p | p ∈ atomSet V E ∧ p < a}
    {p | p ∈ atomSet V E ∧ p < b} (fun _ hp => hp.1) (fun _ hp => hp.1)
    (fun _ hp => ⟨hp.1, hp.2.trans_le h⟩)).2

theorem atomShift_le_total (hs : IsSmoothingWeights V E ω s) (b : ℝ) :
    atomShift V E s b ≤ ∑' p : atomSet V E, s p :=
  (atomWeight_sum_bound hs {p | p ∈ atomSet V E ∧ p < b} (atomSet V E)
    (fun _ hp => hp.1) (fun _ hp => hp) (fun _ hp => hp.1)).2

theorem atomShift_add_weight_le {a b : ℝ} (hs : IsSmoothingWeights V E ω s)
    (ha : a ∈ atomSet V E) (hab : a < b) : atomShift V E s a + s a ≤ atomShift V E s b := by
  classical
  let A := {p : ℝ | p ∈ atomSet V E ∧ p < a}
  let B := {p : ℝ | p ∈ atomSet V E ∧ p < b}
  let f (p : A) : B := ⟨p, p.property.1, p.property.2.trans hab⟩
  let q : B := ⟨a, ha, hab⟩
  have hf : Function.Injective f := fun p q he => Subtype.ext (congrArg (fun (p : B) => (p : ℝ)) he)
  have hAS := (atomWeight_sum_bound hs A (atomSet V E) (fun _ p => p.1) (fun _ p => p)
    (fun _ p => p.1)).1
  have hBS := (atomWeight_sum_bound hs B (atomSet V E) (fun _ p => p.1) (fun _ p => p)
    (fun _ p => p.1)).1
  have hB : atomShift V E s a ≤ atomShift V E s b - s a := by
    apply hAS.tsum_le_of_sum_le
    intro T
    have hN : q ∉ T.image f := by
      rintro hq
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hq
      have he : (p : ℝ) = a := congrArg (fun (p : B) => (p : ℝ)) hp
      exact (ne_of_lt p.property.2) he
    have h := hBS.sum_le_tsum (insert q (T.image f)) (fun p _ => (hs.1 p p.property.1).le)
    rw [Finset.sum_insert hN, Finset.sum_image hf.injOn] at h
    change s a + (∑ p ∈ T, s p) ≤ atomShift V E s b at h
    linarith
  linarith

theorem atomShift_add_weight_le_total (hs : IsSmoothingWeights V E ω s)
    {b : ℝ} (hb : b ∈ atomSet V E) : atomShift V E s b + s b ≤ ∑' p : atomSet V E, s p := by
  exact (atomShift_add_weight_le hs hb (show b < b + 1 by linarith)).trans
    (atomShift_le_total hs (b + 1))

noncomputable def jitter : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance jitter_probability : IsProbabilityMeasure jitter := by
  constructor
  simp [jitter, Real.volume_Icc]

open Classical in
noncomputable def smoothBid (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (s : ℝ → ℝ) (b u : ℝ) : ℝ :=
  b + atomShift V E s b + if b ∈ atomSet V E then s b * u else 0

theorem ae_jitter : ∀ᵐ u ∂jitter, u ∈ Icc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc

theorem smoothBid_bounds (hs : IsSmoothingWeights V E ω s) (b : ℝ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    b ≤ smoothBid V E s b u ∧ smoothBid V E s b u ≤ b + ω := by
  classical
  unfold smoothBid
  split
  · rename_i hb
    have h := atomShift_add_weight_le_total hs hb
    have h0 := atomShift_nonneg hs b
    have hs0 := (hs.1 b hb).le
    exact ⟨by linarith [mul_nonneg hs0 hu.1],
      by linarith [mul_le_of_le_one_right hs0 hu.2, hs.2.2]⟩
  · constructor
    · linarith [atomShift_nonneg hs b]
    · linarith [atomShift_le_total hs b, hs.2.2]

theorem smoothBid_strict_order (hs : IsSmoothingWeights V E ω s) {a b u w : ℝ}
    (hab : a < b) (hu : u ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) :
    smoothBid V E s a u < smoothBid V E s b w := by
  classical
  have hr : b + atomShift V E s b ≤ smoothBid V E s b w := by
    unfold smoothBid
    split
    · rename_i hb
      linarith [mul_nonneg (hs.1 b hb).le hw.1]
    · linarith
  apply lt_of_lt_of_le _ hr
  unfold smoothBid
  split
  · rename_i ha
    have h := atomShift_add_weight_le hs ha hab
    linarith [mul_le_of_le_one_right (hs.1 a ha).le hu.2]
  · linarith [monotone_atomShift hs hab.le]

theorem measurable_smoothBid [∀ i, IsProbabilityMeasure (marginalBid V E i)]
    (hs : IsSmoothingWeights V E ω s) :
    Measurable (fun p : ℝ × ℝ => smoothBid V E s p.1 p.2) := by
  classical
  have hBase : Measurable (fun p : ℝ × ℝ => p.1 + atomShift V E s p.1) :=
    measurable_fst.add ((monotone_atomShift hs).measurable.comp measurable_fst)
  have hWeight : Measurable ((atomSet V E).indicator s) :=
    (measurable_const (a := (0 : ℝ))).measurable_of_countable_ne
      ((countable_atomSet (V := V) (E := E)).mono fun p hp => by
        by_contra h
        exact hp (by simp [Set.indicator_of_notMem h]))
  have hJ := (hWeight.comp measurable_fst).mul measurable_snd
  convert hBase.add hJ using 1
  ext p
  by_cases hp : p.1 ∈ atomSet V E <;> simp [smoothBid, Set.indicator, hp, Function.comp_def]

theorem map_jitter_eq_smoothedBidLaw (b : ℝ) :
    jitter.map (smoothBid V E s b) = smoothedBidLaw V E s b := by
  classical
  unfold smoothedBidLaw
  by_cases hb : b ∈ atomSet V E
  · rw [if_pos hb]
    congr 1
    funext u
    simp [smoothBid, hb]
  · rw [if_neg hb]
    have hFun : smoothBid V E s b = fun _ => b + atomShift V E s b := by
      funext u
      simp [smoothBid, hb]
    rw [hFun, Measure.map_const, measure_univ, one_smul]

noncomputable def smoothingKernel [∀ i, IsProbabilityMeasure (marginalBid V E i)]
    (hs : IsSmoothingWeights V E ω s) : Kernel ℝ ℝ where
  toFun := smoothedBidLaw V E s
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have hMeas := measurable_smoothBid hs
    have h := measurable_measure_prodMk_left (ν := jitter) (hMeas hA)
    convert h using 1
    ext b
    rw [← map_jitter_eq_smoothedBidLaw (V := V) (E := E) (s := s), Measure.map_apply]
    · rfl
    · exact hMeas.comp measurable_prodMk_left
    · exact hA

instance smoothingKernel_markov [∀ i, IsProbabilityMeasure (marginalBid V E i)]
    (hs : IsSmoothingWeights V E ω s) : IsMarkovKernel (smoothingKernel hs) := by
  constructor
  intro b
  change IsProbabilityMeasure (smoothedBidLaw V E s b)
  rw [← map_jitter_eq_smoothedBidLaw]
  exact Measure.isProbabilityMeasure_map ((measurable_smoothBid hs).comp measurable_prodMk_left).aemeasurable

end MultiUnitPoA

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

private theorem tieShare_formula {n : ℕ} (k : ℕ) (β : Fin n → ℝ) (p : ℝ)
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
open LargeSupplyFPA.Asymptotic
open scoped ProbabilityTheory

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable {ω : ℝ} {s : ℝ → ℝ}
variable [∀ i, IsProbabilityMeasure (marginalBid V E i)]

noncomputable def smoothProfile (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (s : ℝ → ℝ) (β u : Fin n → ℝ) : Fin n → ℝ :=
  fun j => smoothBid V E s (β j) (u j)

theorem measurable_smoothProfile (hs : IsSmoothingWeights V E ω s) :
    Measurable (fun x : (Fin n → ℝ) × (Fin n → ℝ) => smoothProfile V E s x.1 x.2) := by
  apply measurable_pi_lambda
  intro j
  have hj : Measurable (fun x : (Fin n → ℝ) × (Fin n → ℝ) => (x.1 j, x.2 j)) :=
    ((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)
  exact (measurable_smoothBid hs).comp hj

theorem map_prod_smoothBid (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hs : IsSmoothingWeights V E ω s) :
    (μ.prod jitter).map (fun x : ℝ × ℝ => smoothBid V E s x.1 x.2) =
      μ.bind (smoothedBidLaw V E s) := by
  ext A hA
  have hm := measurable_smoothBid hs
  change ((μ.prod jitter).map (fun x : ℝ × ℝ => smoothBid V E s x.1 x.2)) A =
    (μ.bind (smoothingKernel hs)) A
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA),
    Measure.bind_apply hA (smoothingKernel hs).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with b
  change _ = smoothedBidLaw V E s b A
  rw [← map_jitter_eq_smoothedBidLaw]
  have hF : Measurable (smoothBid V E s b) := hm.comp measurable_prodMk_left
  rw [Measure.map_apply hF hA]
  rfl

theorem smoothedMarginal_probability (hs : IsSmoothingWeights V E ω s) (i : Fin n) :
    IsProbabilityMeasure (smoothedMarginal V E s i) := by
  rw [smoothedMarginal, ← map_prod_smoothBid _ hs]
  exact Measure.isProbabilityMeasure_map (measurable_smoothBid hs).aemeasurable

theorem map_prod_smoothProfile (hs : IsSmoothingWeights V E ω s) :
    ((Measure.pi (marginalBid V E)).prod (Measure.pi fun _ : Fin n => jitter)).map
      (fun x : (Fin n → ℝ) × (Fin n → ℝ) => smoothProfile V E s x.1 x.2) =
      Measure.pi (smoothedMarginal V E s) := by
  let μ := marginalBid V E
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) μ (fun _ => jitter)
  rw [← he.map_eq, Measure.map_map (measurable_smoothProfile hs) he.measurable]
  let : ∀ i : Fin n, SigmaFinite (((μ i).prod jitter).map
      (fun x : ℝ × ℝ => smoothBid V E s x.1 x.2)) := fun i => by
    rw [map_prod_smoothBid (μ i) hs]
    let := smoothedMarginal_probability hs i
    change SigmaFinite (smoothedMarginal V E s i)
    infer_instance
  change (Measure.pi fun i => (μ i).prod jitter).map
    (fun x j => smoothBid V E s (x j).1 (x j).2) = _
  rw [Measure.pi_map_pi (f := fun _ => fun x : ℝ × ℝ => smoothBid V E s x.1 x.2)
    (fun _ => (measurable_smoothBid hs).aemeasurable)]
  congr 1
  funext i
  exact map_prod_smoothBid (μ i) hs

theorem smoothedBidLaw_singleton_of_atom (hs : IsSmoothingWeights V E ω s)
    {b : ℝ} (hb : b ∈ atomSet V E) (d : ℝ) : smoothedBidLaw V E s b {d} = 0 := by
  rw [← map_jitter_eq_smoothedBidLaw]
  have hF : Measurable (smoothBid V E s b) :=
    (measurable_smoothBid hs).comp measurable_prodMk_left
  rw [Measure.map_apply hF (measurableSet_singleton d)]
  have hInj : Function.Injective (smoothBid V E s b) := by
    intro x y h
    simp only [smoothBid, if_pos hb] at h
    exact mul_left_cancel₀ (hs.1 b hb).ne' (add_left_cancel h)
  have hS : (smoothBid V E s b ⁻¹' {d}).Subsingleton := by
    intro x hx y hy
    exact hInj (hx.trans hy.symm)
  rw [jitter]
  rw [Measure.restrict_apply hS.countable.measurableSet]
  exact (hS.countable.mono Set.inter_subset_left).measure_zero volume

theorem smoothedMarginal_no_atoms (hs : IsSmoothingWeights V E ω s) (i : Fin n) (d : ℝ) :
    smoothedMarginal V E s i {d} = 0 := by
  change ((marginalBid V E i).bind (smoothingKernel hs)) {d} = 0
  rw [Measure.bind_apply (measurableSet_singleton d) (smoothingKernel hs).aemeasurable]
  let A : Set ℝ := {b | b ∉ atomSet V E ∧ b + atomShift V E s b = d}
  have hMono : StrictMono (fun b => b + atomShift V E s b) :=
    strictMono_id.add_monotone (monotone_atomShift hs)
  have hS : A.Subsingleton := fun _ hx _ hy => hMono.injective (hx.2.trans hy.2.symm)
  have hNull : marginalBid V E i A = 0 := by
    by_cases h : A.Nonempty
    · obtain ⟨b, hb⟩ := h
      have he : A = {b} := Set.eq_singleton_iff_unique_mem.mpr
        ⟨hb, fun x hx => hS hx hb⟩
      rw [he]
      by_contra hn
      exact hb.1 ⟨i, hn⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
  have hA : ∀ᵐ b ∂marginalBid V E i, b ∉ A := by
    rw [ae_iff]
    simpa using hNull
  have hz : (fun b => smoothedBidLaw V E s b {d}) =ᵐ[marginalBid V E i] 0 := by
    filter_upwards [hA] with b hb
    by_cases ha : b ∈ atomSet V E
    · exact smoothedBidLaw_singleton_of_atom hs ha d
    · have hne : b + atomShift V E s b ≠ d := fun he => hb ⟨ha, he⟩
      simp [smoothedBidLaw, ha, Measure.dirac_apply', hne, Set.indicator_of_notMem]
  change (∫⁻ b, smoothedBidLaw V E s b {d} ∂marginalBid V E i) = 0
  rw [lintegral_congr_ae hz]
  simp

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Set
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

namespace MultiUnitPoA

private theorem group_full {n : ℕ} (k : ℕ) (xb : Fin n → ℝ) (i : Fin n) (S : Finset (Fin n))
    (hi : i ∈ S) (hS : S.card ≤ k) (hOrder : ∀ j, xb i ≤ xb j → j ∈ S) :
    tieShare k i (xb i) xb = 1 := by
  classical
  let A := Finset.univ.filter fun j => j ≠ i ∧ xb i < xb j
  let T := Finset.univ.filter fun j => j ≠ i ∧ xb j = xb i
  have hd : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro j hj ht
    exact (ne_of_gt (Finset.mem_filter.mp hj).2.2) (Finset.mem_filter.mp ht).2.2
  have hSub : A ∪ T ⊆ S.erase i := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2.1,
        hOrder j (Finset.mem_filter.mp hj).2.2.le⟩
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2.1,
        hOrder j (Finset.mem_filter.mp hj).2.2.ge⟩
  have hc := Finset.card_le_card hSub
  rw [Finset.card_union_of_disjoint hd, Finset.card_erase_of_mem hi] at hc
  have h0 := Finset.card_pos.mpr (show S.Nonempty from ⟨i, hi⟩)
  have hReal : (1 : ℝ) + (A.card : ℝ) + (T.card : ℝ) ≤ k := by
    exact_mod_cast (show 1 + A.card + T.card ≤ k by omega)
  change min (max ((k : ℝ) - A.card) 0 / (1 + (T.card : ℝ))) 1 = 1
  apply min_eq_right
  rw [le_div_iff₀ (by positivity), one_mul]
  exact (show 1 + (T.card : ℝ) ≤ (k : ℝ) - A.card by linarith).trans (le_max_left _ _)

private theorem group_empty {n : ℕ} (k : ℕ) (xb : Fin n → ℝ) (i : Fin n) (S : Finset (Fin n))
    (hS : k ≤ S.card) (hOrder : ∀ j ∈ S, xb i < xb j) :
    tieShare k i (xb i) xb = 0 := by
  classical
  let A := Finset.univ.filter fun j => j ≠ i ∧ xb i < xb j
  have hSub : S ⊆ A := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨fun h => (lt_irrefl _) (h ▸ hOrder j hj), hOrder j hj⟩⟩
  have hc : (k : ℝ) ≤ A.card := by exact_mod_cast hS.trans (Finset.card_le_card hSub)
  unfold tieShare
  change min (max ((k : ℝ) - A.card) 0 / _) 1 = 0
  rw [max_eq_right (sub_nonpos.mpr hc), zero_div, min_eq_left zero_le_one]

noncomputable def groupAbove {n : ℕ} (β : Fin n → ℝ) (b : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => b < β j)

noncomputable def groupEqual {n : ℕ} (β : Fin n → ℝ) (b : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => β j = b)

theorem allocation_of_tied_group {n : ℕ} (k : ℕ) (β γ : Fin n → ℝ) (b : ℝ)
    (hγ : ∀ i j, β i < β j → γ i < γ j) :
    (∑ i ∈ groupEqual β b, tieShare k i (γ i) γ) =
      (min (k - (groupAbove β b).card) (groupEqual β b).card : ℕ) := by
  classical
  let A := groupAbove β b
  let T := groupEqual β b
  let W (j : Fin n) := tieShare k j (γ j) γ
  have hA (j : Fin n) : j ∈ A ↔ b < β j := by simp [A, groupAbove]
  have hT (j : Fin n) : j ∈ T ↔ β j = b := by simp [T, groupEqual]
  change (∑ i ∈ T, W i) = _
  by_cases hAbove : k ≤ A.card
  · rw [Nat.sub_eq_zero_of_le hAbove, min_eq_left (Nat.zero_le _), Nat.cast_zero]
    exact Finset.sum_eq_zero fun i hi => group_empty k γ i A hAbove
      (fun j hj => hγ i j ((hT i).1 hi ▸ (hA j).1 hj))
  have hD : Disjoint A T := Finset.disjoint_left.mpr fun i ha ht =>
    (ne_of_gt ((hA i).1 ha)) ((hT i).1 ht)
  have hCard : (A ∪ T).card = A.card + T.card := Finset.card_union_of_disjoint hD
  by_cases hRoom : (A ∪ T).card ≤ k
  · have hmin : T.card ≤ k - A.card := by omega
    rw [min_eq_right hmin]
    have hWin (i : Fin n) (hi : i ∈ T) : W i = 1 := by
      apply group_full k γ i (A ∪ T) (Finset.mem_union_right _ hi) hRoom
      intro j hj
      have hβ : b ≤ β j := by
        by_contra! h
        have he : β i = b := (hT i).1 hi
        exact (not_lt_of_ge hj) (hγ j i (he.symm ▸ h))
      rcases lt_or_eq_of_le hβ with h | h
      · exact Finset.mem_union_left _ ((hA j).2 h)
      · exact Finset.mem_union_right _ ((hT j).2 h.symm)
    simp [Finset.sum_congr rfl (fun i hi => hWin i hi)]
  · have hk : k ≤ (A ∪ T).card := by omega
    have hkn : k ≤ n := hk.trans (by simpa using (A ∪ T).card_le_univ)
    have hmin : k - A.card ≤ T.card := by omega
    have hkA : A.card ≤ k := by omega
    rw [min_eq_left hmin, Nat.cast_sub hkA]
    have hWin (i : Fin n) (hi : i ∈ A) : W i = 1 := by
      apply group_full k γ i A hi hkA
      intro j hj
      apply (hA j).2
      by_contra! h
      exact (not_lt_of_ge hj) (hγ j i (h.trans_lt ((hA i).1 hi)))
    have hLose (i : Fin n) (hi : i ∉ A ∪ T) : W i = 0 := by
      apply group_empty k γ i (A ∪ T) hk
      have hi' : β i < b := lt_of_le_of_ne (le_of_not_gt (fun h => hi
        (Finset.mem_union_left _ ((hA i).2 h)))) (fun h => hi (Finset.mem_union_right _ ((hT i).2 h)))
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hγ i j (hi'.trans ((hA j).1 hj))
      · exact hγ i j (((hT j).1 hj).symm ▸ hi')
    have hSum := sum_tieShare k γ hkn
    have hIncluded : (∑ i ∈ A ∪ T, W i) = k := by
      change (∑ i, W i) = _ at hSum
      exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hLose i hi)).trans hSum
    rw [Finset.sum_union hD] at hIncluded
    have hAsum : (∑ i ∈ A, W i) = A.card := by
      calc
        _ = ∑ _i ∈ A, (1 : ℝ) := Finset.sum_congr rfl hWin
        _ = _ := by simp
    linarith

theorem tieShare_of_tied_group {n : ℕ} (k : ℕ) (β : Fin n → ℝ) (i : Fin n) (b : ℝ)
    (hi : β i = b) :
    tieShare k i b β =
      ((min (k - (groupAbove β b).card) (groupEqual β b).card : ℕ) : ℝ) /
        (groupEqual β b).card := by
  classical
  let A := groupAbove β b
  let T := groupEqual β b
  have hiT : i ∈ T := by simp [T, groupEqual, hi]
  have ht0 : 0 < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨i, hiT⟩
  have hA : (Finset.univ.filter fun j => j ≠ i ∧ b < β j) = A := by
    ext j
    simp only [A, groupAbove, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨fun he => by simp [he, hi] at h, h⟩⟩
  have hT : (Finset.univ.filter fun j => j ≠ i ∧ β j = b) = T.erase i := by
    ext j
    simp [T, groupEqual]
  have ht : 1 + ((T.erase i).card : ℝ) = T.card := by
    have htn := Finset.card_pos.mpr ⟨i, hiT⟩
    exact_mod_cast (show 1 + (T.erase i).card = T.card by rw [Finset.card_erase_of_mem hiT]; omega)
  unfold tieShare
  rw [hA, hT, ht]
  have hCast : ((k - A.card : ℕ) : ℝ) = max ((k : ℝ) - A.card) 0 := by
    rcases le_total A.card k with h | h
    · rw [Nat.cast_sub h, max_eq_left (sub_nonneg.mpr (by exact_mod_cast h))]
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, max_eq_right (sub_nonpos.mpr (by exact_mod_cast h))]
  rw [← hCast]
  change min (((k - A.card : ℕ) : ℝ) / (T.card : ℝ)) 1 =
    ((min (k - A.card) T.card : ℕ) : ℝ) / T.card
  rw [Nat.cast_min, ← min_div_div_right ht0.le, div_self ht0.ne']

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable {ω : ℝ} {s : ℝ → ℝ}
variable [∀ i, IsProbabilityMeasure (marginalBid V E i)]

private theorem tieShare_reindex (k : ℕ) (e : Equiv.Perm (Fin n)) (i : Fin n)
    (b : ℝ) (β : Fin n → ℝ) :
    tieShare k i b (β ∘ e) = tieShare k (e i) b β := by
  classical
  have hC (P : ℝ → Prop) [DecidablePred P] :
      (Finset.univ.filter (fun j => j ≠ i ∧ P ((β ∘ e) j))).card =
        (Finset.univ.filter (fun j => j ≠ e i ∧ P (β j))).card := by
    have hMap : (Finset.univ.filter (fun j => j ≠ i ∧ P ((β ∘ e) j))).map e.toEmbedding =
        Finset.univ.filter (fun j => j ≠ e i ∧ P (β j)) := by
      ext j
      rw [Finset.mem_map]
      constructor
      · rintro ⟨l, hl, rfl⟩
        obtain ⟨hl₀, hl₁⟩ := (Finset.mem_filter.mp hl).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hl₀ (e.injective h), hl₁⟩
      · intro hj
        obtain ⟨hj₀, hj₁⟩ := (Finset.mem_filter.mp hj).2
        refine ⟨e.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, e.apply_symm_apply j⟩
        · exact fun h => hj₀ ((e.apply_symm_apply j).symm.trans (congrArg e h))
        · simpa only [Function.comp_apply, e.apply_symm_apply]
    rw [← hMap, Finset.card_map]
  unfold tieShare
  rw [hC (fun y => b < y), hC (fun y => y = b)]

omit [∀ i, IsProbabilityMeasure (marginalBid V E i)] in
private theorem eq_under_same_bid_permutation (k : ℕ)
    (β : Fin n → ℝ) (i j : Fin n) (hij : β i = β j) :
    (∫ u, tieShare k i (smoothProfile V E s β u i) (smoothProfile V E s β u)
        ∂Measure.pi (fun _ : Fin n => jitter)) =
    (∫ u, tieShare k j (smoothProfile V E s β u j) (smoothProfile V E s β u)
        ∂Measure.pi (fun _ : Fin n => jitter)) := by
  classical
  let e := Equiv.swap i j
  let ψ := (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e).symm
  have hp := (measurePreserving_piCongrLeft (fun _ : Fin n => jitter) e).symm
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e)
  let f (u : Fin n → ℝ) := tieShare k i (smoothProfile V E s β u i) (smoothProfile V E s β u)
  change (∫ u, f u ∂Measure.pi (fun _ : Fin n => jitter)) = _
  rw [← hp.integral_comp' f]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have hSwap (l : Fin n) : β (e l) = β l := by
    by_cases h₀ : l = i
    · subst l
      simp [e, hij]
    · by_cases h₁ : l = j
      · subst l
        simp [e, hij]
      · rw [show e l = l from Equiv.swap_apply_of_ne_of_ne h₀ h₁]
  have hψ (l : Fin n) : ψ u l = u (e l) := by
    exact Equiv.piCongrLeft_symm_apply _ e u l
  have heq : smoothProfile V E s β (ψ u) = smoothProfile V E s β u ∘ e := by
    ext l
    simp only [smoothProfile, Function.comp_apply, hψ, hSwap]
  change tieShare k i (smoothProfile V E s β (ψ u) i) (smoothProfile V E s β (ψ u)) = _
  rw [heq, tieShare_reindex]
  simp [e]

theorem integrate_tie_share_smooth (k : ℕ) (hs : IsSmoothingWeights V E ω s) (β : Fin n → ℝ)
    (i : Fin n) :
    (∫ u, tieShare k i (smoothProfile V E s β u i) (smoothProfile V E s β u)
        ∂Measure.pi (fun _ : Fin n => jitter)) = tieShare k i (β i) β := by
  classical
  let T := groupEqual β (β i)
  let ν := Measure.pi (fun _ : Fin n => jitter)
  let F (j : Fin n) (u : Fin n → ℝ) :=
    tieShare k j (smoothProfile V E s β u j) (smoothProfile V E s β u)
  have hI (j : Fin n) : Integrable (F j) ν := by
    have hM : Measurable (F j) := by
      have hM : Measurable (fun u => smoothProfile V E s β u) :=
        (measurable_smoothProfile hs).comp measurable_prodMk_left
      have hP : Measurable (fun u => (smoothProfile V E s β u j, smoothProfile V E s β u)) :=
        ((measurable_pi_apply j).comp hM).prodMk hM
      exact Measurable.comp (f := fun u => (smoothProfile V E s β u j, smoothProfile V E s β u))
        (g := fun p : ℝ × (Fin n → ℝ) => tieShare k j p.1 p.2)
        (measurable_tieShare_joint k j) hP
    apply (integrable_const (1 : ℝ)).mono' hM.aestronglyMeasurable
    exact Eventually.of_forall fun u => by
      change ‖tieShare k j (smoothProfile V E s β u j) (smoothProfile V E s β u)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (tieShare_nonneg k j _ _)]
      exact tieShare_le_one k j _ _
  have hSum : (∫ u, ∑ j ∈ T, F j u ∂ν) = (min (k - (groupAbove β (β i)).card) T.card : ℕ) := by
    trans ∫ _u : Fin n → ℝ, ((min (k - (groupAbove β (β i)).card) T.card : ℕ) : ℝ) ∂ν
    · apply integral_congr_ae
      have hJitter : ∀ᵐ u ∂ν, ∀ j, u j ∈ Icc (0 : ℝ) 1 :=
        eventually_all.mpr fun j => (Measure.tendsto_eval_ae_ae (i := j)).eventually ae_jitter
      filter_upwards [hJitter] with u hu
      exact allocation_of_tied_group k β (smoothProfile V E s β u) (β i)
        (fun l j h => smoothBid_strict_order hs h (hu l) (hu j))
    · simp
  rw [integral_finsetSum _ (fun j _ => hI j)] at hSum
  have hEq (j : Fin n) (hj : j ∈ T) : (∫ u, F j u ∂ν) = ∫ u, F i u ∂ν :=
    eq_under_same_bid_permutation k β j i (Finset.mem_filter.mp hj).2
  rw [Finset.sum_congr rfl hEq, Finset.sum_const, nsmul_eq_mul] at hSum
  have hi : i ∈ T := by simp [T, groupEqual]
  have hPos : 0 < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
  rw [tieShare_of_tied_group k β i (β i) rfl]
  apply (eq_div_iff hPos.ne').2
  simpa only [mul_comm] using hSum

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace MultiUnitPoA

private theorem integral_update_jitter {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin n => jitter))) :
    (∫ t, ∫ u, f (Function.update u i t) ∂Measure.pi (fun _ : Fin n => jitter) ∂jitter) =
      ∫ u, f u ∂Measure.pi (fun _ : Fin n => jitter) := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let ν : Measure (Fin n → ℝ) := Measure.pi fun _ => jitter
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    have hPres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => jitter) i).symm e
    have hSplit (t : ℝ) :
        (∫ u, f (Function.update u i t) ∂Measure.pi (fun _ : Fin (n + 1) => jitter)) =
          ∫ u, f (i.insertNth (α := fun _ => ℝ) t u) ∂ν := by
      rw [← hPres.integral_comp' (fun u => f (Function.update u i t))]
      have hEq (p : ℝ × (Fin n → ℝ)) :
          Function.update (e.symm p) i t = i.insertNth (α := fun _ => ℝ) t p.2 := by
        funext j
        apply (i.forall_iff_succAbove (P := fun j =>
          Function.update (e.symm p) i t j = i.insertNth (α := fun _ => ℝ) t p.2 j)).2
        constructor
        · simp
        · intro j
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.insertNth_apply_succAbove, Fin.succAbove_ne]
      simp_rw [hEq]
      rw [integral_fun_snd (fun u => f (i.insertNth (α := fun _ => ℝ) t u))]
      simp [ν]
    simp_rw [hSplit]
    rw [← hPres.integral_comp' f]
    rw [integral_prod (fun p => f (e.symm p)) (hPres.integrable_comp_of_integrable hf)]
    rfl

theorem smoothing_average_alloc {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) {ω : ℝ} {s : ℝ → ℝ}
    [∀ i, IsProbabilityMeasure (marginalBid V E i)] (hs : IsSmoothingWeights V E ω s)
    (i : Fin n) (b : ℝ) :
    alloc k V E i b = ∫ t, smoothedAlloc k V E s i (smoothBid V E s b t) ∂jitter := by
  classical
  let μ := Measure.pi (marginalBid V E)
  let ν := Measure.pi (fun _ : Fin n => jitter)
  let G (β u : Fin n → ℝ) (t : ℝ) :=
    tieShare k i (smoothBid V E s b t) (smoothProfile V E s β u)
  have hG : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ => G p.1.1 p.1.2 p.2) := by
    have hb : Measurable (smoothBid V E s b) :=
      (measurable_smoothBid hs).comp measurable_prodMk_left
    have hP : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ =>
        (smoothBid V E s b p.2, smoothProfile V E s p.1.1 p.1.2)) :=
      (hb.comp measurable_snd).prodMk ((measurable_smoothProfile hs).comp measurable_fst)
    exact Measurable.comp
      (f := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ =>
        (smoothBid V E s b p.2, smoothProfile V E s p.1.1 p.1.2))
      (g := fun p : ℝ × (Fin n → ℝ) => tieShare k i p.1 p.2)
      (measurable_tieShare_joint k i) hP
  have hGInt : Integrable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ => G p.1.1 p.1.2 p.2)
      ((μ.prod ν).prod jitter) := by
    apply (integrable_const (1 : ℝ)).mono' hG.aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      change ‖tieShare k i (smoothBid V E s b p.2) (smoothProfile V E s p.1.1 p.1.2)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (tieShare_nonneg k i _ _)]
      exact tieShare_le_one k i _ _
  have hForm (t : ℝ) : smoothedAlloc k V E s i (smoothBid V E s b t) =
      ∫ p, G p.1 p.2 t ∂μ.prod ν := by
    unfold smoothedAlloc allocOf
    rw [← map_prod_smoothProfile hs]
    have hP : Measurable (fun β : Fin n → ℝ => (smoothBid V E s b t, β)) :=
      measurable_const.prodMk measurable_id
    have hFun : Measurable (tieShare k i (smoothBid V E s b t)) :=
      Measurable.comp (f := fun β => (smoothBid V E s b t, β))
        (g := fun p : ℝ × (Fin n → ℝ) => tieShare k i p.1 p.2)
        (measurable_tieShare_joint k i) hP
    exact integral_map (measurable_smoothProfile hs).aemeasurable hFun.aestronglyMeasurable
  simp_rw [hForm]
  rw [← integral_prod_symm _ hGInt, integral_prod _ hGInt]
  have hJ : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => ∫ t, G p.1 p.2 t ∂jitter)
      (μ.prod ν) := hGInt.integral_prod_left
  rw [integral_prod _ hJ]
  unfold alloc allocOf
  apply integral_congr_ae
  apply Eventually.of_forall
  intro β
  let β' := Function.update β i b
  let f (u : Fin n → ℝ) :=
    tieShare k i (smoothProfile V E s β' u i) (smoothProfile V E s β' u)
  have hEq (u : Fin n → ℝ) (t : ℝ) : G β u t = f (Function.update u i t) := by
    have ht : smoothProfile V E s β' (Function.update u i t) i = smoothBid V E s b t := by
      simp [smoothProfile, β']
    unfold f G
    rw [ht]
    apply tieShare_congr
    intro j hj
    simp [smoothProfile, β', Function.update_of_ne hj]
  have hF : Measurable f := by
    have hm : Measurable (fun u => smoothProfile V E s β' u) :=
      (measurable_smoothProfile hs).comp measurable_prodMk_left
    have hP : Measurable (fun u => (smoothProfile V E s β' u i, smoothProfile V E s β' u)) :=
      ((measurable_pi_apply i).comp hm).prodMk hm
    exact Measurable.comp (f := fun u => (smoothProfile V E s β' u i, smoothProfile V E s β' u))
      (g := fun p : ℝ × (Fin n → ℝ) => tieShare k i p.1 p.2)
      (measurable_tieShare_joint k i) hP
  have hf : Integrable f ν := by
    apply (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    exact Eventually.of_forall fun u => by
      change ‖tieShare k i (smoothProfile V E s β' u i) (smoothProfile V E s β' u)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (tieShare_nonneg k i _ _)]
      exact tieShare_le_one k i _ _
  have hSlice : Integrable (fun p : (Fin n → ℝ) × ℝ => G β p.1 p.2) (ν.prod jitter) := by
    have hM : Measurable (fun p : (Fin n → ℝ) × ℝ => G β p.1 p.2) :=
      hG.comp (g := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ => G p.1.1 p.1.2 p.2)
        (f := fun p : (Fin n → ℝ) × ℝ => ((β, p.1), p.2))
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    apply (integrable_const (1 : ℝ)).mono' hM.aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      change ‖tieShare k i (smoothBid V E s b p.2) (smoothProfile V E s β p.1)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (tieShare_nonneg k i _ _)]
      exact tieShare_le_one k i _ _
  change tieShare k i b β = ∫ u, ∫ t, G β u t ∂jitter ∂ν
  rw [← integral_prod _ hSlice, integral_prod_symm _ hSlice]
  simp_rw [hEq]
  rw [integral_update_jitter i f hf]
  change tieShare k i b β = ∫ u, f u ∂ν
  have h := integrate_tie_share_smooth k hs β' i
  change (∫ u, f u ∂ν) = tieShare k i (β' i) β' at h
  rw [h, show β' i = b by simp [β']]
  exact tieShare_congr k i b (fun j hj => by simp [β', Function.update_of_ne hj])

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

theorem tieShare_eq_one {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) (β : Fin n → ℝ)
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

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic
open scoped ProbabilityTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MultiUnitPoA

private theorem tieShare_eq_zero_if_count {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) (β : Fin n → ℝ)
    (h : k ≤ (Finset.univ.filter fun j => j ≠ i ∧ b < β j).card) :
    tieShare k i b β = 0 := by
  unfold tieShare
  have hR : (k : ℝ) ≤ ((Finset.univ.filter fun j => j ≠ i ∧ b < β j).card : ℝ) := by exact_mod_cast h
  rw [max_eq_right (sub_nonpos.mpr hR), zero_div, min_eq_left zero_le_one]

theorem smooth_alloc_le_perturbation {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} {ω : ℝ} {s : ℝ → ℝ}
    [∀ i, IsProbabilityMeasure (marginalBid V E i)]
    (hs : IsSmoothingWeights V E ω s) (i : Fin n) (d : ℝ) {η : ℝ} (hη : 0 < η) :
    smoothedAlloc k V E s i d ≤ alloc k V E i (d + η) := by
  classical
  let μ := Measure.pi (marginalBid V E)
  let ν := Measure.pi (fun _ : Fin n => jitter)
  let Z := (Fin n → ℝ) × (Fin n → ℝ)
  let A (p : Z) := tieShare k i d (smoothProfile V E s p.1 p.2)
  let C (p : Z) := tieShare k i (d + η) p.1
  have hM (b : ℝ) : Measurable (tieShare k i b) := by
    have hP : Measurable (fun β : Fin n → ℝ => (b, β)) := measurable_const.prodMk measurable_id
    exact Measurable.comp (f := fun β => (b, β))
      (g := fun p : ℝ × (Fin n → ℝ) => tieShare k i p.1 p.2)
      (measurable_tieShare_joint k i) hP
  have hI (f : Z → ℝ) (hf : Measurable f) (hB : ∀ p, 0 ≤ f p ∧ f p ≤ 1) :
      Integrable f (μ.prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    exact Eventually.of_forall fun p => by rw [Real.norm_eq_abs, abs_of_nonneg (hB p).1]; exact (hB p).2
  have hPoint : A ≤ᵐ[μ.prod ν] C := by
    have hJ : ∀ᵐ u ∂ν, ∀ j, u j ∈ Icc (0 : ℝ) 1 :=
      eventually_all.mpr fun j => (Measure.tendsto_eval_ae_ae (i := j)).eventually ae_jitter
    have hAE : ∀ᵐ p : Z ∂μ.prod ν, ∀ j, p.2 j ∈ Icc (0 : ℝ) 1 :=
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).tendsto_ae.eventually hJ
    filter_upwards [hAE] with p hp
    let S := Finset.univ.filter fun j => j ≠ i ∧ d + η ≤ p.1 j
    by_cases hS : S.card < k
    · have hh := tieShare_eq_one k i (d + η) p.1 hS
      change A p ≤ tieShare k i (d + η) p.1
      rw [hh]
      exact tieShare_le_one k i _ _
    · have hSub : S ⊆ Finset.univ.filter (fun j => j ≠ i ∧ d < smoothProfile V E s p.1 p.2 j) := by
        intro j hj
        obtain ⟨hj₁, hj₂⟩ := (Finset.mem_filter.mp hj).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₁, (lt_add_of_pos_right _ hη).trans_le
          (hj₂.trans (smoothBid_bounds hs (p.1 j) (hp j)).1)⟩
      change tieShare k i d (smoothProfile V E s p.1 p.2) ≤ C p
      rw [tieShare_eq_zero_if_count k i d _ ((le_of_not_gt hS).trans (Finset.card_le_card hSub))]
      exact tieShare_nonneg k i _ _
  have h := integral_mono_ae
    (hI A ((hM d).comp (measurable_smoothProfile hs)) (fun _ => ⟨tieShare_nonneg k i _ _, tieShare_le_one k i _ _⟩))
    (hI C ((hM (d + η)).comp measurable_fst) (fun _ => ⟨tieShare_nonneg k i _ _, tieShare_le_one k i _ _⟩))
    hPoint
  unfold smoothedAlloc alloc allocOf
  rw [← map_prod_smoothProfile hs, integral_map (measurable_smoothProfile hs).aemeasurable (hM d).aestronglyMeasurable]
  have hc : (∫ p, C p ∂μ.prod ν) = ∫ β, tieShare k i (d + η) β ∂μ := by
    exact (integral_fun_fst (μ := μ) (ν := ν) (tieShare k i (d + η))).trans (by simp)
  exact h.trans_eq hc

theorem smoothed_utility_le_original_bound {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} {ω : ℝ} {s : ℝ → ℝ}
    [∀ i, IsProbabilityMeasure (marginalBid V E i)]
    (hs : IsSmoothingWeights V E ω s) (i : Fin n) {v c : ℝ} (hv : 0 ≤ v)
    (hUtil : ∀ b : ℝ, 0 ≤ b → utility k V E i v b ≤ c)
    (d : ℝ) (hd : 0 ≤ d) : (v - d) * smoothedAlloc k V E s i d ≤ c := by
  have hX0 (b : ℝ) : 0 ≤ smoothedAlloc k V E s i b :=
    integral_nonneg (fun _ => tieShare_nonneg k i b _)
  have hc : 0 ≤ c := by
    have h := hUtil 0 le_rfl
    unfold utility at h
    rw [sub_zero] at h
    exact (mul_nonneg hv (alloc_nonneg (V := V) (E := E) k i 0)).trans h
  rcases le_total v d with h | h
  · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (hX0 d)).trans hc
  · apply le_of_forall_pos_le_add
    intro η hη
    have ha := smooth_alloc_le_perturbation k hs i d hη
    have hC := hUtil (d + η) (by linarith)
    have hl := alloc_le_one (V := V) (E := E) k i (d + η)
    have hB := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr h)
    have he := mul_le_mul_of_nonneg_left hl hη.le
    unfold utility at hC
    nlinarith

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic
open scoped ProbabilityTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable {ω : ℝ} {s : ℝ → ℝ}
variable [∀ i, IsProbabilityMeasure (marginalBid V E i)]

noncomputable def smoothStrategy (hs : IsSmoothingWeights V E ω s) (i : Fin n) : Kernel ℝ ℝ :=
  smoothingKernel hs ∘ₖ E i

private theorem smoothStrategy_apply (hs : IsSmoothingWeights V E ω s) (i : Fin n) [IsMarkovKernel (E i)] (v : ℝ) :
    smoothStrategy hs i v = ((E i v).prod jitter).map (fun p : ℝ × ℝ => smoothBid V E s p.1 p.2) := by
  unfold smoothStrategy
  rw [Kernel.comp_apply]
  exact (map_prod_smoothBid (E i v) hs).symm

theorem smoothStrategy_marginal (hs : IsSmoothingWeights V E ω s) (hV : IsValueProfile V)
    (hE : IsStrategyProfile E) (i : Fin n) :
    marginalBid V (smoothStrategy hs) i = smoothedMarginal V E s i := by
  let := hV i
  let := (hE i).1
  change (smoothingKernel hs ∘ₖ E i) ∘ₘ V i = smoothingKernel hs ∘ₘ (E i ∘ₘ V i)
  exact Measure.comp_assoc.symm

theorem smoothStrategy_isStrategy (hs : IsSmoothingWeights V E ω s) (hE : IsStrategyProfile E) :
    IsStrategyProfile (smoothStrategy hs) := by
  intro i
  let := (hE i).1
  constructor
  · unfold smoothStrategy
    infer_instance
  · intro v
    rw [smoothStrategy_apply hs i v, Measure.map_apply (measurable_smoothBid hs) measurableSet_Iio]
    have h0 : ∀ᵐ b ∂E i v, (0 : ℝ) ≤ b := by
      rw [ae_iff]
      simpa only [not_le, Set.Iio] using (hE i).2 v
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := E i v) (ν := jitter)).tendsto_ae.eventually h0, (Measure.quasiMeasurePreserving_snd (μ := E i v) (ν := jitter)).tendsto_ae.eventually ae_jitter]
      with p hB hJ
    exact not_lt_of_ge (hB.trans (smoothBid_bounds hs p.1 hJ).1)

theorem smoothStrategy_bound (hs : IsSmoothingWeights V E ω s) (hE : IsStrategyProfile E)
    (i : Fin n) (v t : ℝ) (ht : E i v (Iic t) = 1) : smoothStrategy hs i v (Iic (t + ω)) = 1 := by
  let := (hE i).1
  rw [smoothStrategy_apply hs i v, Measure.map_apply (measurable_smoothBid hs) measurableSet_Iic]
  have h0 : ∀ᵐ b ∂E i v, b ≤ t :=
    (ae_mem_iff_measure_eq measurableSet_Iic.nullMeasurableSet).2 (ht.trans measure_univ.symm)
  rw [← measure_univ (μ := (E i v).prod jitter)]
  apply (ae_mem_iff_measure_eq ((measurable_smoothBid hs) measurableSet_Iic).nullMeasurableSet).1
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := E i v) (ν := jitter)).tendsto_ae.eventually h0, (Measure.quasiMeasurePreserving_snd (μ := E i v) (ν := jitter)).tendsto_ae.eventually ae_jitter] with p hB hJ
  exact (smoothBid_bounds hs p.1 hJ).2.trans (add_le_add_left hB ω)

theorem smoothStrategy_alloc (hs : IsSmoothingWeights V E ω s) (hV : IsValueProfile V)
    (hE : IsStrategyProfile E) (k : ℕ) (i : Fin n) :
    alloc k V (smoothStrategy hs) i = smoothedAlloc k V E s i := by
  unfold alloc smoothedAlloc
  rw [show marginalBid V (smoothStrategy hs) = smoothedMarginal V E s from
    funext (smoothStrategy_marginal hs hV hE)]

private theorem smooth_alloc_measurable (hs : IsSmoothingWeights V E ω s) (k : ℕ) (i : Fin n) :
    Measurable (smoothedAlloc k V E s i) := by
  let : ∀ j, IsProbabilityMeasure (smoothedMarginal V E s j) := smoothedMarginal_probability hs
  exact (measurable_tieShare_joint k i).stronglyMeasurable.integral_prod_right'.measurable

private theorem smooth_alloc_mem_Icc (hs : IsSmoothingWeights V E ω s) (k : ℕ)
    (i : Fin n) (b : ℝ) : smoothedAlloc k V E s i b ∈ Icc (0 : ℝ) 1 := by
  let : ∀ j, IsProbabilityMeasure (smoothedMarginal V E s j) := smoothedMarginal_probability hs
  constructor
  · exact integral_nonneg (fun _ => tieShare_nonneg k i b _)
  · have h := integral_mono_of_nonneg (μ := Measure.pi (smoothedMarginal V E s))
      (f := tieShare k i b) (g := fun _ => 1)
      (Eventually.of_forall (tieShare_nonneg k i b)) (integrable_const _)
      (Eventually.of_forall (tieShare_le_one k i b))
    simpa [smoothedAlloc, allocOf] using h

theorem smoothStrategy_welfare (hs : IsSmoothingWeights V E ω s) (hV : IsValueProfile V)
    (hE : IsStrategyProfile E) (k : ℕ) : welfare k V E = welfare k V (smoothStrategy hs) := by
  unfold welfare
  apply Finset.sum_congr rfl
  intro i _
  let := (hE i).1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro v
  dsimp only
  rw [smoothStrategy_apply hs i v, smoothStrategy_alloc hs hV hE k i,
    integral_map (measurable_smoothBid hs).aemeasurable (smooth_alloc_measurable hs k i).aestronglyMeasurable]
  congr 1
  let f (p : ℝ × ℝ) := smoothedAlloc k V E s i (smoothBid V E s p.1 p.2)
  have hI : Integrable f ((E i v).prod jitter) := by
    apply (integrable_const (1 : ℝ)).mono' ((smooth_alloc_measurable hs k i).comp
      (measurable_smoothBid hs)).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      have h := smooth_alloc_mem_Icc hs k i (smoothBid V E s p.1 p.2)
      change ‖smoothedAlloc k V E s i (smoothBid V E s p.1 p.2)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2
  change _ = ∫ p, f p ∂(E i v).prod jitter
  rw [integral_prod f hI]
  apply integral_congr_ae
  exact Eventually.of_forall fun b => smoothing_average_alloc k V E hs i b

private theorem smoothStrategy_utility_bound (hs : IsSmoothingWeights V E ω s)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hω : 0 ≤ ω) (k : ℕ) (i : Fin n) (v : ℝ)
    (hI : Integrable (utility k V E i v) (E i v)) :
    Integrable (utility k V (smoothStrategy hs) i v) (smoothStrategy hs i v) ∧
      (∫ b, utility k V E i v b ∂E i v) - ω ≤
        ∫ d, utility k V (smoothStrategy hs) i v d ∂smoothStrategy hs i v := by
  let := (hE i).1
  let μ := E i v
  let f (p : ℝ × ℝ) := (v - smoothBid V E s p.1 p.2) *
    smoothedAlloc k V E s i (smoothBid V E s p.1 p.2)
  let a (p : ℝ × ℝ) := smoothedAlloc k V E s i (smoothBid V E s p.1 p.2)
  have ha : Measurable a := (smooth_alloc_measurable hs k i).comp (measurable_smoothBid hs)
  have hf : Measurable f := (measurable_const.sub (measurable_smoothBid hs)).mul ha
  have hAbs : Integrable (fun p : ℝ × ℝ => |v - p.1| * a p) (μ.prod jitter) := by
    have hNonneg (p : ℝ × ℝ) : 0 ≤ |v - p.1| * a p :=
      mul_nonneg (abs_nonneg _) (smooth_alloc_mem_Icc hs k i _).1
    apply (integrable_prod_iff
      ((measurable_const.sub measurable_fst).abs.mul ha).aestronglyMeasurable).2
    constructor
    · exact Eventually.of_forall fun b => (integrable_const (|v - b| : ℝ)).mono'
        ((measurable_const (a := |v - b|)).mul
          (ha.comp measurable_prodMk_left)).aestronglyMeasurable
        (Eventually.of_forall fun t => by
          change ‖|v - b| * a (b, t)‖ ≤ _
          rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg (b, t))]
          exact mul_le_of_le_one_right (abs_nonneg _) (smooth_alloc_mem_Icc hs k i _).2)
    · have hEq (b : ℝ) :
          (∫ t, ‖|v - b| * a (b, t)‖ ∂jitter) = |utility k V E i v b| := by
        have hPoint (t : ℝ) : ‖|v - b| * a (b, t)‖ = |v - b| * a (b, t) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg (b, t))]
        simp_rw [hPoint]
        rw [integral_const_mul]
        change |v - b| * (∫ t, smoothedAlloc k V E s i (smoothBid V E s b t) ∂jitter) = _
        rw [← smoothing_average_alloc k V E hs i b, utility, abs_mul,
          abs_of_nonneg (alloc_nonneg k i b)]
      exact hI.abs.congr (Eventually.of_forall fun b => (hEq b).symm)
  have hG : Integrable f (μ.prod jitter) := by
    apply (hAbs.add (integrable_const ω)).mono' hf.aestronglyMeasurable
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ)).tendsto_ae.eventually ae_jitter] with p hp
    have hb := smoothBid_bounds hs p.1 hp
    have ha0 := (smooth_alloc_mem_Icc hs k i (smoothBid V E s p.1 p.2)).1
    have ha1 := (smooth_alloc_mem_Icc hs k i (smoothBid V E s p.1 p.2)).2
    have hDiff : |v - smoothBid V E s p.1 p.2| ≤ |v - p.1| + ω := by
      calc
        _ ≤ |v - p.1| + |p.1 - smoothBid V E s p.1 p.2| := by
          have he : v - p.1 + (p.1 - smoothBid V E s p.1 p.2) =
              v - smoothBid V E s p.1 p.2 := by ring
          exact he ▸ abs_add_le (v - p.1) (p.1 - smoothBid V E s p.1 p.2)
        _ ≤ _ := by rw [abs_of_nonpos (sub_nonpos.mpr hb.1)]; linarith [hb.2]
    change ‖(v - smoothBid V E s p.1 p.2) * a p‖ ≤ |v - p.1| * a p + ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha0]
    calc
      _ ≤ (|v - p.1| + ω) * a p := mul_le_mul_of_nonneg_right hDiff ha0
      _ ≤ _ := by rw [add_mul]; linarith [mul_le_of_le_one_right hω ha1]
  have hM : Measurable (utility k V (smoothStrategy hs) i v) := by
    unfold utility
    rw [smoothStrategy_alloc hs hV hE k i]
    exact (measurable_const.sub measurable_id).mul (smooth_alloc_measurable hs k i)
  have hMap := smoothStrategy_apply hs i v
  have hfEq : f = fun p : ℝ × ℝ => utility k V (smoothStrategy hs) i v (smoothBid V E s p.1 p.2) := by
    funext p
    unfold f utility
    rw [smoothStrategy_alloc hs hV hE k i]
  have hIt : Integrable (utility k V (smoothStrategy hs) i v) (smoothStrategy hs i v) := by
    rw [hMap, integrable_map_measure hM.aestronglyMeasurable (measurable_smoothBid hs).aemeasurable]
    rw [hfEq] at hG
    exact hG
  refine ⟨hIt, ?_⟩
  rw [hMap, integral_map (measurable_smoothBid hs).aemeasurable hM.aestronglyMeasurable]
  have hRewrite : (∫ p, utility k V (smoothStrategy hs) i v (smoothBid V E s p.1 p.2)
      ∂μ.prod jitter) = ∫ p, f p ∂μ.prod jitter :=
    congrArg (fun g => ∫ p, g p ∂μ.prod jitter) hfEq.symm
  rw [hRewrite, integral_prod f hG]
  rw [← show (∫ _ : ℝ, ω ∂μ) = ω by simp,
    ← integral_sub hI (integrable_const ω)]
  apply integral_mono_ae (hI.sub (integrable_const ω)) hG.integral_prod_left
  apply Eventually.of_forall
  intro b
  have hA : Integrable (fun t => a (b, t)) jitter := by
    apply (integrable_const (1 : ℝ)).mono' (ha.comp measurable_prodMk_left).aestronglyMeasurable
    exact Eventually.of_forall fun t => by
      have hx := smooth_alloc_mem_Icc hs k i (smoothBid V E s b t)
      change ‖smoothedAlloc k V E s i (smoothBid V E s b t)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
  suffices hb : (∫ t, (v - b) * a (b, t) - ω ∂jitter) ≤ ∫ t, f (b, t) ∂jitter by
    rw [integral_sub (hA.const_mul _) (integrable_const ω), integral_const_mul,
      show (∫ _ : ℝ, ω ∂jitter) = ω by simp] at hb
    change (v - b) * (∫ t, smoothedAlloc k V E s i (smoothBid V E s b t) ∂jitter) - ω ≤ _ at hb
    rwa [← smoothing_average_alloc k V E hs i b] at hb
  have hbI : Integrable (fun t => f (b, t)) jitter := by
    apply (integrable_const (|v - b| + ω)).mono' (hf.comp measurable_prodMk_left).aestronglyMeasurable
    filter_upwards [ae_jitter] with t ht
    have hB := smoothBid_bounds hs b ht
    have hA' := smooth_alloc_mem_Icc hs k i (smoothBid V E s b t)
    have hDif : |v - smoothBid V E s b t| ≤ |v - b| + ω := by
      apply abs_le.mpr
      constructor <;> linarith [le_abs_self (v - b), neg_le_abs (v - b), hB.1, hB.2]
    change ‖(v - smoothBid V E s b t) * a (b, t)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hA'.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) hA'.2).trans hDif
  apply integral_mono_ae ((hA.const_mul (v - b)).sub (integrable_const ω)) hbI
  filter_upwards [ae_jitter] with t ht
  have hShift := (smoothBid_bounds hs b ht).2
  have hBounds := smooth_alloc_mem_Icc hs k i (smoothBid V E s b t)
  change (v - b) * a (b, t) - ω ≤ (v - smoothBid V E s b t) * a (b, t)
  have h1 := mul_le_mul_of_nonneg_right
    (show v - b - ω ≤ v - smoothBid V E s b t by linarith) hBounds.1
  have h2 := mul_le_of_le_one_right hω hBounds.2
  linarith [sub_mul (v - b) ω (a (b, t))]

theorem smoothing_with_nonnegative_values {n : ℕ} (k : ℕ)
    (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) (ε : ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hBNE : IsApproxBNE k V E ε)
    (hValue : ∀ i, ∀ v ∈ (V i).support, 0 ≤ v) (ω : ℝ) (hω : 0 < ω) :
    ∃ Et : Fin n → Kernel ℝ ℝ, IsStrategyProfile Et ∧
      IsApproxBNE k V Et (ε + ω) ∧
      IsAtomless V Et ∧
      welfare k V E = welfare k V Et ∧
      (∀ i v t, E i v (Set.Iic t) = 1 → Et i v (Set.Iic (t + ω)) = 1) := by
  let : ∀ j, IsProbabilityMeasure (marginalBid V E j) := marginalBid_probability hV hE
  obtain ⟨s, hs⟩ := exists_smoothingWeights (V := V) (E := E) hω
  refine ⟨smoothStrategy hs, smoothStrategy_isStrategy hs hE, ?_, ?_,
    smoothStrategy_welfare hs hV hE k, smoothStrategy_bound hs hE⟩
  · intro i v hv
    obtain ⟨hI, hD⟩ := hBNE i v hv
    obtain ⟨hIt, hIneq⟩ := smoothStrategy_utility_bound hs hV hE hω.le k i v hI
    refine ⟨hIt, ?_⟩
    intro d hd
    have hDev : ∀ b, 0 ≤ b → utility k V E i v b ≤ (∫ t, utility k V E i v t ∂E i v) + ε := by
      intro b hb
      linarith [hD b hb]
    have h := smoothed_utility_le_original_bound k hs i (hValue i v hv) hDev d hd
    have h0 : utility k V (smoothStrategy hs) i v d =
        (v - d) * smoothedAlloc k V E s i d := by
      unfold utility
      rw [smoothStrategy_alloc hs hV hE k i]
    rw [h0]
    linarith
  · intro i b
    rw [smoothStrategy_marginal hs hV hE]
    exact smoothedMarginal_no_atoms hs i b

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Set
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Theorem3Nonnegative

theorem solution {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) (ε : ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hBNE : IsApproxBNE k V E ε)
    (hValue : ∀ i, ∀ v ∈ (V i).support, 0 ≤ v) (ω : ℝ) (hω : 0 < ω) :
    ∃ Et : Fin n → Kernel ℝ ℝ, IsStrategyProfile Et ∧
      IsApproxBNE k V Et (ε + ω) ∧
      IsAtomless V Et ∧ welfare k V E = welfare k V Et ∧
      (∀ i v t, E i v (Iic t) = 1 → Et i v (Iic (t + ω)) = 1) :=
  smoothing_with_nonnegative_values k V E ε hV hE hBNE hValue ω hω


end Theorem3Nonnegative

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

theorem liminf_eq_one_of_subseq_bounds (r : ℕ → ℝ)
    (hr0 : ∀ k, 0 ≤ r k) (hr1 : ∀ k, r k ≤ 1)
    (hsub : ∀ s : ℕ → ℕ, StrictMono s → ∀ c > (0 : ℝ),
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ 1 - c ≤ liminf (r ∘ s ∘ θ) atTop) :
    liminf r atTop = 1 := by
  have hb : IsBoundedUnder (· ≥ ·) atTop r := isBoundedUnder_of ⟨0, hr0⟩
  have htop : liminf r atTop ≤ 1 := by
    apply liminf_le_of_le hb
    intro b h
    obtain ⟨k, hk⟩ := h.exists
    exact hk.trans (hr1 k)
  apply le_antisymm htop
  by_contra! hlt
  let a := (liminf r atTop + 1) / 2
  have ha : liminf r atTop < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hfreq : ∃ᶠ k in atTop, r k < a := by
    by_contra! hn
    have hc : IsCoboundedUnder (· ≥ ·) atTop r :=
      ⟨1, fun b hb => by
        obtain ⟨k, hk⟩ := (eventually_map.mp hb).exists
        exact hk.trans (hr1 k)⟩
    exact (not_le_of_gt ha) (le_liminf_of_le hc hn)
  obtain ⟨s, hs, hslt⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨θ, _, hθ⟩ := hsub s hs ((1 - a) / 2) (by linarith)
  have hu : liminf (r ∘ s ∘ θ) atTop ≤ a := by
    apply liminf_le_of_le (show IsBoundedUnder (· ≥ ·) atTop (r ∘ s ∘ θ) from
      isBoundedUnder_of ⟨0, fun k => hr0 (s (θ k))⟩)
    intro b hb
    obtain ⟨k, hk⟩ := hb.exists
    exact hk.trans (hslt (θ k)).le
  linarith

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

namespace Lemma4

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


end Lemma4

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic MultiUnitPoA
open scoped BigOperators

set_option autoImplicit false

namespace Lemma5

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


end Lemma5

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false

namespace MultiUnitPoA

noncomputable def revenueAt {n : ℕ} (k : ℕ) (β : Fin n → ℝ) : ℝ :=
  ∑ i, β i * tieShare k i (β i) β

theorem measurable_revenueAt {n : ℕ} (k : ℕ) : Measurable (revenueAt (n := n) k) := by
  have hTerm (i : Fin n) : Measurable (fun β : Fin n → ℝ => β i * tieShare k i (β i) β) := by
    have hPair : Measurable (fun β : Fin n → ℝ => (β i, β)) :=
      (measurable_pi_apply i).prodMk measurable_id
    have hTie := (measurable_tieShare_joint k i).comp hPair
    exact (measurable_pi_apply i).mul hTie
  exact Finset.measurable_sum Finset.univ (fun i _ => hTerm i)

theorem expected_revenue_lower {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) [∀ i, IsProbabilityMeasure (marginalBid V E i)]
    (hk : 0 < k) (hkn : k ≤ n) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hInt : Integrable (revenueAt k) (Measure.pi (marginalBid V E)))
    (hNonneg : 0 ≤ᵐ[Measure.pi (marginalBid V E)] revenueAt k) :
    (k : ℝ) * (hi - lo * kthBidCDF k V E lo - ∫ b in lo..hi, kthBidCDF k V E b) ≤
      ∫ β, revenueAt k β ∂Measure.pi (marginalBid V E) := by
  let μ := Measure.pi (marginalBid V E)
  let clipped (β : Fin n → ℝ) := max 0 (min hi (revenueAt k β / k))
  have hhi : 0 ≤ hi := hlo.trans hlh
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hcl0 : ∀ β, 0 ≤ clipped β := fun _ => le_max_left _ _
  have hcl1 : ∀ β, clipped β ≤ hi := fun _ => max_le hhi (min_le_left _ _)
  have hClipped : Integrable clipped μ := by
    apply (integrable_const hi).mono' (f := clipped) _ _
    · exact (measurable_const.max (measurable_const.min
        ((measurable_revenueAt k).div_const (k : ℝ)))).aestronglyMeasurable
    · exact Eventually.of_forall fun β => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hcl0 β)]
        exact hcl1 β
  have hClLe : (∫ β, (k : ℝ) * clipped β ∂μ) ≤ ∫ β, revenueAt k β ∂μ := by
    apply integral_mono_ae (hClipped.const_mul _) hInt
    filter_upwards [hNonneg] with β hβ
    apply (le_div_iff₀' hkR).1
    exact max_le (div_nonneg hβ hkR.le) (min_le_right _ _)
  rw [integral_const_mul] at hClLe
  have hTail (b : ℝ) (hb : b ∈ Ioc 0 hi) :
      1 - kthBidCDF k V E b ≤ μ.real {β | b ≤ clipped β} := by
    rw [kthBidCDF_eq_count]
    have hm : MeasurableSet {β : Fin n → ℝ | bidCount Finset.univ b β < k} :=
      measurableSet_lt (measurable_bidCount Finset.univ b) measurable_const
    rw [← probReal_compl_eq_one_sub hm]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro β h
    have hcR : (k : ℝ) ≤ bidCount Finset.univ b β := le_of_not_gt h
    rw [bidCount_eq_card] at hcR
    have hc : k ≤ numAbove b β := by
      unfold numAbove
      exact_mod_cast hcR
    exact (le_min hb.2 (average_bid_ge_of_count k β hk hkn b hc).le).trans (le_max_right _ _)
  let F := kthBidCDF k V E
  have hmF : Monotone F := monotone_kthBidCDF k V E
  have hI₀ : IntervalIntegrable F volume 0 lo := hmF.intervalIntegrable
  have hI₁ : IntervalIntegrable F volume lo hi := hmF.intervalIntegrable
  have hTailInt : IntegrableOn (fun b => μ.real {β | b ≤ clipped β}) (Ioc 0 hi) volume := by
    apply (integrable_const (1 : ℝ)).mono' (f := fun b => μ.real {β | b ≤ clipped β})
    · exact (show Antitone (fun b => μ.real {β | b ≤ clipped β}) from
          fun _ _ hab => measureReal_mono (fun _ h => hab.trans h)).measurable.aestronglyMeasurable
    · exact Eventually.of_forall fun _ => by rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hLo : (∫ b in 0..lo, F b) ≤ lo * F lo := by
    have h := intervalIntegral.integral_mono_on hlo hI₀
      (intervalIntegrable_const (c := F lo)) (fun b hb => hmF (show b ≤ lo from hb.2))
    simpa [mul_comm] using h
  have hPrice : hi - lo * F lo - (∫ b in lo..hi, F b) ≤ ∫ β, clipped β ∂μ := by
    rw [hClipped.integral_eq_integral_Ioc_meas_le (Eventually.of_forall hcl0)
      (Eventually.of_forall hcl1)]
    have hArea :
        (∫ b in 0..hi, (1 - F b)) ≤ ∫ b in Ioc 0 hi, μ.real {β | b ≤ clipped β} := by
      rw [intervalIntegral.integral_of_le hhi]
      exact integral_mono_ae
        ((intervalIntegrable_const.sub (hI₀.trans hI₁)).1) hTailInt
        ((ae_restrict_mem measurableSet_Ioc).mono hTail)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hI₀.trans hI₁),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
      ← intervalIntegral.integral_add_adjacent_intervals hI₀ hI₁] at hArea
    linarith
  exact (mul_le_mul_of_nonneg_left hPrice hkR.le).trans hClLe

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic
open scoped ProbabilityTheory

set_option autoImplicit false

namespace MultiUnitPoA

theorem ae_bid_bounds {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    {H κ ω : ℝ} (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    (hA1 : Assumption1 H κ V) (hOver : OverbidAtMost ω V E) (i : Fin n) :
    ∀ᵐ p ∂pairLaw V E i, p.1 ∈ Icc (0 : ℝ) H ∧ p.2 ∈ Icc 0 (p.1 + ω) := by
  let := hV i
  let := (hE i).1
  unfold pairLaw
  apply (Measure.ae_compProd_iff (p := fun p : ℝ × ℝ => p.1 ∈ Icc (0 : ℝ) H ∧
      p.2 ∈ Icc 0 (p.1 + ω)) ?_).2
  · filter_upwards [ae_value_mem_Icc hV hA1 i, Measure.support_mem_ae (μ := V i)] with v hv hs
    have h0 : ∀ᵐ b ∂E i v, 0 ≤ b := by
      rw [ae_iff]
      simpa only [not_le, Set.Iio] using (hE i).2 v
    have h1 : ∀ᵐ b ∂E i v, b ≤ v + ω :=
      (ae_mem_iff_measure_eq measurableSet_Iic.nullMeasurableSet).2
        ((hOver i v hs).trans (measure_univ (μ := E i v)).symm)
    filter_upwards [h0, h1] with b hb0 hb1
    exact ⟨hv, hb0, hb1⟩
  · exact (measurable_fst measurableSet_Icc).inter <|
      (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.add measurable_const))

theorem ae_bid_profile_bounds {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    {H κ ω : ℝ} (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    (hA1 : Assumption1 H κ V) (hOver : OverbidAtMost ω V E) :
    ∀ᵐ β ∂Measure.pi (marginalBid V E), ∀ i, β i ∈ Icc (0 : ℝ) (H + ω) := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  let : ∀ i, IsMarkovKernel (E i) := fun i => (hE i).1
  let : ∀ i, IsProbabilityMeasure (marginalBid V E i) := marginalBid_probability hV hE
  apply eventually_all.2
  intro i
  have h : ∀ᵐ b ∂marginalBid V E i, b ∈ Icc (0 : ℝ) (H + ω) := by
    rw [← pairLaw_map_snd V E i]
    apply (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).2
    filter_upwards [ae_bid_bounds hV hE hA1 hOver i] with p hp
    exact ⟨hp.2.1, hp.2.2.trans (add_le_add_left hp.1.2 ω)⟩
  exact (Measure.tendsto_eval_ae_ae (μ := marginalBid V E) (i := i)).eventually h

theorem integrable_revenueAt {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
    {H κ ω : ℝ} (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    (hA1 : Assumption1 H κ V) (hOver : OverbidAtMost ω V E) :
    Integrable (revenueAt k) (Measure.pi (marginalBid V E)) ∧
      0 ≤ᵐ[Measure.pi (marginalBid V E)] revenueAt k := by
  let : ∀ i, IsProbabilityMeasure (marginalBid V E i) := marginalBid_probability hV hE
  have hBounds := ae_bid_profile_bounds hV hE hA1 hOver
  have hNonneg : 0 ≤ᵐ[Measure.pi (marginalBid V E)] revenueAt k := by
    filter_upwards [hBounds] with β hβ
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hβ i).1 (tieShare_nonneg k i _ _)
  refine ⟨(integrable_const ((n : ℝ) * (H + ω))).mono'
    (measurable_revenueAt k).aestronglyMeasurable ?_, hNonneg⟩
  filter_upwards [hNonneg, hBounds] with β h0 hβ
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  calc
    revenueAt k β ≤ ∑ _i : Fin n, (H + ω) := Finset.sum_le_sum fun i _ =>
      (mul_le_of_le_one_right (hβ i).1 (tieShare_le_one k i _ _)).trans (hβ i).2
    _ = _ := by simp [mul_add]

noncomputable def avgUtility {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (i : Fin n) (v : ℝ) : ℝ :=
  ∫ b, utility k V E i v b ∂E i v

set_option maxHeartbeats 800000 in
theorem welfare_eq_utility_add_revenue {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    {H κ ω : ℝ} (hH : 0 ≤ H) (hω : 0 ≤ ω)
    (hA1 : Assumption1 H κ V) (hOver : OverbidAtMost ω V E) :
    welfare k V E = (∑ i, ∫ v, avgUtility k V E i v ∂V i) +
      ∫ β, revenueAt k β ∂Measure.pi (marginalBid V E) := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  let : ∀ i, IsMarkovKernel (E i) := fun i => (hE i).1
  let : ∀ i, IsProbabilityMeasure (pairLaw V E i) := pairLaw_probability hV hE
  let : ∀ i, IsProbabilityMeasure (marginalBid V E i) := marginalBid_probability hV hE
  let μ := Measure.pi (pairLaw V E)
  let X (i : Fin n) (x : Fin n → ℝ × ℝ) := tieShare k i (x i).2 (fun j => (x j).2)
  let U (i : Fin n) (x : Fin n → ℝ × ℝ) := ((x i).1 - (x i).2) * X i x
  let R (i : Fin n) (x : Fin n → ℝ × ℝ) := (x i).2 * X i x
  have hX (i : Fin n) : Measurable (X i) := measurable_profile_tieShare k i
  have hVal (i : Fin n) :
      ∀ᵐ x ∂μ, (x i).1 ∈ Icc (0 : ℝ) H ∧ (x i).2 ∈ Icc 0 ((x i).1 + ω) :=
    (Measure.tendsto_eval_ae_ae (μ := pairLaw V E) (i := i)).eventually (ae_bid_bounds hV hE hA1 hOver i)
  have hR (i : Fin n) : Integrable (R i) μ := by
    apply (integrable_const (H + ω)).mono'
      ((measurable_snd.comp (measurable_pi_apply i)).mul (hX i)).aestronglyMeasurable
    filter_upwards [hVal i] with x h
    change ‖(x i).2 * X i x‖ ≤ H + ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h.2.1 (tieShare_nonneg k i _ _))]
    exact (mul_le_of_le_one_right h.2.1 (tieShare_le_one k i _ _)).trans
      (h.2.2.trans (add_le_add_left h.1.2 ω))
  have hU (i : Fin n) : Integrable (U i) μ := by
    apply (integrable_const (H + ω)).mono'
      (((measurable_fst.comp (measurable_pi_apply i)).sub
        (measurable_snd.comp (measurable_pi_apply i))).mul (hX i)).aestronglyMeasurable
    filter_upwards [hVal i] with x h
    have hB : |(x i).1 - (x i).2| ≤ H + ω := abs_le.mpr ⟨by linarith [h.2.2],
      by linarith [h.1.2, h.2.1]⟩
    change ‖((x i).1 - (x i).2) * X i x‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tieShare_nonneg k i _ _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (tieShare_le_one k i _ _)).trans hB
  have hSingle (i : Fin n) :
      (∫ v, avgUtility k V E i v ∂V i) = ∫ x, U i x ∂μ := by
    rw [show (∫ x, U i x ∂μ) = (∫ p, utility k V E i p.1 p.2 ∂pairLaw V E i)
      from integrate_allocation k V E hV hE i (fun p => p.1 - p.2) (hU i)]
    have hI : Integrable (fun p : ℝ × ℝ => utility k V E i p.1 p.2) (pairLaw V E i) := by
      apply (integrable_const (H + ω)).mono'
      · exact ((measurable_fst.sub measurable_snd).mul
          ((measurable_alloc k V E i).comp measurable_snd)).aestronglyMeasurable
      filter_upwards [ae_bid_bounds hV hE hA1 hOver i] with p hp
      have hB : |p.1 - p.2| ≤ H + ω :=
        abs_le.mpr ⟨by linarith [hp.2.2], by linarith [hp.1.2, hp.2.1]⟩
      unfold utility
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (alloc_nonneg k i p.2)]
      exact (mul_le_of_le_one_right (abs_nonneg _) (alloc_le_one k i p.2)).trans hB
    exact (Measure.integral_compProd hI).symm
  rw [welfare_eq_joint k V E hV hE hA1,
    ← pairProfile_map_snd V E hV hE,
    integral_map measurable_snd_profile.aemeasurable (measurable_revenueAt k).aestronglyMeasurable]
  simp_rw [hSingle]
  change (∫ x, ∑ i, (x i).1 * X i x ∂μ) =
    (∑ i, ∫ x, U i x ∂μ) + ∫ x, ∑ i, R i x ∂μ
  rw [← integral_finsetSum _ (fun i _ => hU i),
    ← integral_add (integrable_finsetSum _ (fun i _ => hU i))
      (integrable_finsetSum _ (fun i _ => hR i))]
  apply integral_congr_ae
  filter_upwards with x
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [U, R]
  ring

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic
open scoped ProbabilityTheory

set_option autoImplicit false

namespace MultiUnitPoA

theorem approxBNE_error_nonneg {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} {ε : ℝ} (i : Fin n)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hBNE : IsApproxBNE k V E ε) : 0 ≤ ε := by
  let := hV i
  let := (hE i).1
  obtain ⟨v, hv⟩ := (show ∀ᵐ v ∂V i, v ∈ (V i).support from Measure.support_mem_ae).exists
  obtain ⟨hInt, hDev⟩ := hBNE i v hv
  have h0 : ∀ᵐ b ∂E i v, 0 ≤ b := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using (hE i).2 v
  have hInt' := integral_mono_ae (hInt.sub (integrable_const ε))
    (integrable_const (avgUtility k V E i v)) (h0.mono fun b hb => hDev b hb)
  rw [integral_sub' hInt (integrable_const ε)] at hInt'
  have h := (show (∫ b, utility k V E i v b ∂E i v) - ε ≤
    (∫ b, utility k V E i v b ∂E i v) by simpa [avgUtility] using hInt')
  linarith

private theorem avgUtility_add_omega_nonneg {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} {ω ε : ℝ}
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hω : 0 ≤ ω)
    (hOver : OverbidAtMost ω V E) (hBNE : IsApproxBNE k V E ε)
    (i : Fin n) {v : ℝ} (hv : v ∈ (V i).support) :
    0 ≤ avgUtility k V E i v + ω := by
  let := (hE i).1
  let : ∀ j, IsProbabilityMeasure (marginalBid V E j) := marginalBid_probability hV hE
  have hBid : ∀ᵐ b ∂E i v, b ≤ v + ω :=
    (ae_mem_iff_measure_eq measurableSet_Iic.nullMeasurableSet).2
      ((hOver i v hv).trans (measure_univ (μ := E i v)).symm)
  have h := integral_mono_ae (integrable_const (-ω)) (hBNE i v hv).1
    (hBid.mono (fun b hb => show -ω ≤ utility k V E i v b from by
      have h0 : -ω ≤ v - b := by linarith
      calc
        -ω = -ω * 1 := (mul_one _).symm
        _ ≤ -ω * alloc k V E i b := mul_le_mul_of_nonpos_left (alloc_le_one k i b) (neg_nonpos.mpr hω)
        _ ≤ _ := mul_le_mul_of_nonneg_right h0 (alloc_nonneg k i b)))
  have h' : -ω ≤ avgUtility k V E i v := by simpa [avgUtility] using h
  linarith

theorem fixed_auction_welfare_lower {n : ℕ} (k : ℕ) {V : Fin n → Measure ℝ}
    {E : Fin n → Kernel ℝ ℝ} {H κ ω ε lo hi Δ : ℝ}
    (hk : 0 < k) (hkn : k ≤ n) (hH : 0 ≤ H) (hω : 0 ≤ ω) (hΔ : 0 < Δ)
    (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hV : IsValueProfile V) (hE : IsStrategyProfile E)
    (hA1 : Assumption1 H κ V) (hOver : OverbidAtMost ω V E) (hBNE : IsApproxBNE k V E ε) :
    kthBidCDF k V E hi * optWelfare k V ≤ welfare k V E + (n : ℝ) * ω +
      (k : ℝ) * (lo * kthBidCDF k V E lo + (∫ b in lo..hi, kthBidCDF k V E b) + ε + Δ) := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  let : ∀ i, IsMarkovKernel (E i) := fun i => (hE i).1
  let : ∀ i, IsProbabilityMeasure (marginalBid V E i) := marginalBid_probability hV hE
  let U (i : Fin n) (v : ℝ) := avgUtility k V E i v + ω
  let F := kthBidCDF k V E
  let error := lo * F lo + (∫ b in lo..hi, F b) + ε + Δ
  let price := hi - lo * F lo - (∫ b in lo..hi, F b)
  have hε : 0 ≤ ε := approxBNE_error_nonneg k ⟨0, hk.trans_le hkn⟩ hV hE hBNE
  have hError : 0 ≤ error := by
    have hArea := (cdf_area_bounds k V E hlh).1
    dsimp [error]
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hlo measureReal_nonneg) hArea) hε) hΔ.le
  have hPrice : 0 ≤ price := by
    have hArea := (cdf_area_bounds k V E hlh).2
    have hLo := mul_le_of_le_one_right hlo (measureReal_le_one (μ := Measure.pi (marginalBid V E))
      (s := {β | numAbove lo β < k}))
    change lo * F lo ≤ lo at hLo
    dsimp only [price]
    linarith
  have hUi (i : Fin n) (v : ℝ) (hv : v ∈ (V i).support) : 0 ≤ U i v :=
    avgUtility_add_omega_nonneg k hV hE hω hOver hBNE i hv
  have hDev (i : Fin n) (v : ℝ) (hv : v ∈ (V i).support) :
      F hi * v ≤ U i v + price + error := by
    have hF0 : 0 ≤ F hi := measureReal_nonneg
    have hF1 : F hi ≤ 1 := measureReal_le_one
    have hΔF : F hi * Δ ≤ Δ := mul_le_of_le_one_left hΔ.le hF1
    have hf : F hi * v ≤ U i v + hi + ε + Δ := by
      by_cases hvs : hi + Δ ≤ v
      · have hs := (hBNE i v hv).2 (hi + Δ) (by linarith)
        have ht := mul_le_mul_of_nonneg_left
          ((Fact3.solution k V E hV hE hi (hlo.trans hlh) i).1 Δ hΔ)
          (sub_nonneg.mpr hvs)
        change (v - (hi + Δ)) * F hi ≤ (v - (hi + Δ)) * alloc k V E i (hi + Δ) at ht
        change (v - (hi + Δ)) * alloc k V E i (hi + Δ) - ε ≤ avgUtility k V E i v at hs
        have hhiF := mul_le_of_le_one_left (hlo.trans hlh) hF1
        dsimp [U]
        linarith [mul_sub (F hi) v (hi + Δ), mul_add (F hi) hi Δ,
          mul_comm (F hi) (v - (hi + Δ))]
      · have ht := mul_le_mul_of_nonneg_left (le_of_not_ge hvs) hF0
        have hhiF := mul_le_of_le_one_left (hlo.trans hlh) hF1
        linarith [hUi i v hv, mul_add (F hi) hi Δ]
    dsimp only [price, error]
    linarith
  have hPt :
      ∀ᵐ v ∂Measure.pi V, F hi * topKSum k v ≤ (∑ i, U i (v i)) + (k : ℝ) * (price + error) := by
    have hA : ∀ᵐ v ∂Measure.pi V, ∀ i, v i ∈ (V i).support :=
      eventually_all.mpr fun i => (Measure.tendsto_eval_ae_ae (μ := V)).eventually Measure.support_mem_ae
    filter_upwards [hA] with v hv
    exact topK_comparison k v (fun i => U i (v i)) (F hi) price error
      measureReal_nonneg hPrice hError (fun i => hUi i (v i) (hv i)) (fun i => hDev i (v i) (hv i))
  have hU (i : Fin n) : Integrable (avgUtility k V E i) (V i) := by
    have hPair := ae_bid_bounds hV hE hA1 hOver i
    rw [pairLaw, Measure.ae_compProd_iff] at hPair
    swap
    · exact (measurable_fst measurableSet_Icc).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd (measurable_fst.add measurable_const)))
    have hF : StronglyMeasurable (fun p : ℝ × ℝ => utility k V E i p.1 p.2) :=
      ((measurable_fst.sub measurable_snd).mul
        ((measurable_alloc k V E i).comp measurable_snd)).stronglyMeasurable
    apply (integrable_const (H + ω)).mono' (f := avgUtility k V E i)
    · exact hF.integral_kernel_prod_right'.aestronglyMeasurable
    · filter_upwards [hPair] with v hv
      exact (norm_integral_le_of_norm_le_const (hv.mono fun b hb => by
        unfold utility
        have hB : |v - b| ≤ H + ω := abs_le.mpr ⟨by linarith [hb.2.2], by linarith [hb.1.2, hb.2.1]⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (alloc_nonneg k i b)]
        exact (mul_le_of_le_one_right (abs_nonneg _) (alloc_le_one k i b)).trans hB)).trans_eq (by simp)
  have hUI (i : Fin n) : Integrable (fun v => U i (v i)) (Measure.pi V) :=
    (measurePreserving_eval V i).integrable_comp_of_integrable ((hU i).add (integrable_const ω))
  have hInt := integral_mono_ae ((integrable_topKSum k hH hV hA1).const_mul (F hi))
    ((integrable_finsetSum _ (fun i _ => hUI i)).add
      (integrable_const ((k : ℝ) * (price + error)))) hPt
  rw [integral_const_mul, integral_add' (integrable_finsetSum _ (fun i _ => hUI i))
    (integrable_const _), integral_finsetSum _ (fun i _ => hUI i)] at hInt
  simp only [integral_const, probReal_univ, one_smul] at hInt
  have hMarg (i : Fin n) : (∫ v, U i (v i) ∂Measure.pi V) =
      (∫ v, avgUtility k V E i v ∂V i) + ω := by
    change (∫ v, U i (Function.eval i v) ∂Measure.pi V) = _
    rw [← integral_map (measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval V i).map_eq]
    · exact integral_add (hU i) (integrable_const ω) |>.trans (by simp)
    · rw [(measurePreserving_eval V i).map_eq]
      exact ((hU i).add (integrable_const ω)).aestronglyMeasurable
  simp_rw [hMarg, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin] at hInt
  obtain ⟨hRI, hR0⟩ := integrable_revenueAt k hV hE hA1 hOver
  have hr := expected_revenue_lower k V E hk hkn hlo hlh hRI hR0
  rw [welfare_eq_utility_add_revenue k V E hV hE hH hω hA1 hOver]
  change F hi * optWelfare k V ≤ _
  change (k : ℝ) * price ≤ _ at hr
  change F hi * optWelfare k V ≤ _ at hInt
  change F hi * optWelfare k V ≤ _ + (k : ℝ) * error
  linarith [mul_add (k : ℝ) price error]

end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Set
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Theorem1

private theorem optimal_welfare_lower {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (hkn : k ≤ n) (hV : IsValueProfile V) {H κ : ℝ}
    (hH : 0 < H) (hA1 : Assumption1 H κ V) :
    (k : ℝ) * (κ * (H / 2) ^ 2) ≤ optWelfare k V := by
  let : ∀ i, IsProbabilityMeasure (V i) := hV
  classical
  obtain ⟨S, hS, _⟩ := max_subset k (fun _ : Fin n => (0 : ℝ)) hkn
  have hInd (i : Fin n) : Integrable (fun v : ℝ => v) (V i) := by
    refine (integrable_const H).mono' measurable_id.aestronglyMeasurable ?_
    filter_upwards [ae_value_mem_Icc hV hA1 i] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg hv.1]
    exact hv.2
  have hValue (i : Fin n) : κ * (H / 2) ^ 2 ≤ ∫ v, v ∂V i := by
    let J := Ioo (H / 2) (H / 2 + H / 2)
    have hJ : MeasurableSet J := measurableSet_Ioo
    have h := integral_mono_ae ((integrable_const (H / 2 : ℝ)).indicator hJ) (hInd i) (by
      filter_upwards [ae_value_mem_Icc hV hA1 i] with v hv
      by_cases hj : v ∈ J
      · simpa only [indicator_of_mem hj] using hj.1.le
      · simpa only [indicator_of_notMem hj] using hv.1)
    rw [integral_indicator_const _ hJ, smul_eq_mul] at h
    have hMass := (hA1 i).2 (H / 2) (by positivity) (H / 2) ⟨by positivity, by linarith⟩
    calc
      _ = (κ * (H / 2)) * (H / 2) := by ring
      _ ≤ (V i).real J * (H / 2) := mul_le_mul_of_nonneg_right hMass.le (by positivity)
      _ ≤ _ := h
  have hSInt (i : Fin n) : Integrable (Function.eval i) (Measure.pi V) :=
    (measurePreserving_eval V i).integrable_comp_of_integrable (hInd i)
  have hsum : (∫ v, ∑ i ∈ S, v i ∂Measure.pi V) ≤ optWelfare k V := by
    apply integral_mono (integrable_finsetSum _ (fun i _ => hSInt i))
      (integrable_topKSum k hH.le hV hA1)
    intro v
    unfold topKSum
    exact le_ciSup (f := fun T : {T : Finset (Fin n) // T.card ≤ k} =>
      ∑ i ∈ T.1, v i) (Set.finite_range _).bddAbove ⟨S, hS.le⟩
  have hMarg (i : Fin n) : (∫ v, v i ∂Measure.pi V) = ∫ x, x ∂V i := by
    have h := integral_map (μ := Measure.pi V) (f := fun x : ℝ => x)
      (measurable_pi_apply i).aemeasurable (by
        rw [(measurePreserving_eval V i).map_eq]
        exact (hInd i).aestronglyMeasurable)
    rw [(measurePreserving_eval V i).map_eq] at h
    exact h.symm
  rw [integral_finsetSum _ (fun i _ => hSInt i)] at hsum
  simp_rw [hMarg] at hsum
  apply le_trans _ hsum
  simpa only [Finset.sum_const, nsmul_eq_mul, hS] using
    (Finset.sum_le_sum (s := S) (fun i _ => hValue i))

private theorem tendsto_overbid_budget (n : ℕ → ℕ) (ω : ℕ → ℝ)
    (hn : ∀ k, k < n k) (hω : ∀ k, 0 < ω k)
    (hSmall : ω =o[atTop] fun k => (k : ℝ) / (n k : ℝ)) :
    Tendsto (fun k => (n k : ℝ) * ω k / k) atTop (𝓝 0) ∧ Tendsto ω atTop (𝓝 0) := by
  have hEq (k : ℕ) : ω k / ((k : ℝ) / (n k : ℝ)) = (n k : ℝ) * ω k / k := by
    rw [div_div_eq_mul_div, mul_comm (ω k)]
  have hT₀ : Tendsto (fun k => (n k : ℝ) * ω k / k) atTop (𝓝 0) :=
    hSmall.tendsto_div_nhds_zero.congr hEq
  refine ⟨hT₀, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT₀ ?_ ?_⟩
  · exact Eventually.of_forall fun k => (hω k).le
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    apply (le_div_iff₀ hk').2
    rw [mul_comm (ω k)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hn k).le) (hω k).le

private theorem liminf_lower_of_eventual_bound (f g : ℕ → ℝ) (L : ℝ)
    (hf : Tendsto f atTop (𝓝 L)) (hfg : f ≤ᶠ[atTop] g) (hg : ∀ l, g l ≤ 1) :
    L ≤ liminf g atTop := by
  by_contra! h
  have hm : liminf g atTop < (L + liminf g atTop) / 2 := by linarith
  have hmid : (L + liminf g atTop) / 2 < L := by linarith
  have hEv : ∀ᶠ l in atTop, (L + liminf g atTop) / 2 ≤ g l := by
    filter_upwards [hf.eventually (eventually_ge_nhds hmid), hfg] with l hl₀ hl₁
    exact hl₀.trans hl₁
  have hc : IsCoboundedUnder (· ≥ ·) atTop g := ⟨1, fun b hb => by
    obtain ⟨l, hl⟩ := (eventually_map.mp hb).exists
    exact hl.trans (hg l)⟩
  exact hm.not_ge (le_liminf_of_le hc hEv)

theorem solution (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ) :
    ∃ ζ : ℝ, 0 < ζ ∧
      ∀ (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
        (εs : ℕ → ℝ) (ε : ℝ),
        IsAuctionSequence n V E →
        (∀ k, Assumption1 H κ (V k)) →
        (∀ k, IsApproxBNE k (V k) (E k) (εs k)) →
        Assumption3 n V E →
        Tendsto εs atTop (𝓝 ε) →
        ∀ (c : ℝ), 0 ≤ c →
        ∀ (lo hi : ℕ → ℝ) (φ : ℕ → ℕ), IsExtremizing n V E lo hi φ →
        (∃ L : ℝ, Tendsto (fun l => ∫ b in lo (φ l)..hi (φ l),
            kthBidCDF (φ l) (V (φ l)) (E (φ l)) b) atTop (𝓝 L) ∧ L ≤ c) →
        1 - c / ζ - ε / ζ ≤
          Filter.liminf (fun l => welfareRatio (φ l) (V (φ l)) (E (φ l))) atTop := by
  let ζ := κ * (H / 2) ^ 2
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  refine ⟨ζ, hζ, ?_⟩
  intro n V E εs ε hseq hA1 hBNE hA3 hε c _ lo hi φ hext hArea
  obtain ⟨L, hL, hLc⟩ := hArea
  obtain ⟨ω, hω, hωsmall, hOver⟩ := hA3
  obtain ⟨hωN, hωL⟩ := tendsto_overbid_budget n ω hseq.1 hω hωsmall
  let F (k : ℕ) := kthBidCDF k (V k) (E k)
  let Δ (k : ℕ) := (1 : ℝ) / ((k : ℝ) + 1)
  let A (l : ℕ) := ∫ b in lo (φ l)..hi (φ l), F (φ l) b
  let err (l : ℕ) :=
    (2 * H * F (φ l) (lo (φ l)) + A l + εs (φ l) + Δ (φ l) +
      (n (φ l) : ℝ) * ω (φ l) / φ l) / ζ
  let g (l : ℕ) := welfareRatio (φ l) (V (φ l)) (E (φ l))
  have hφ := hext.1.tendsto_atTop
  have hΔ : Tendsto Δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hErr : Tendsto err atTop (𝓝 ((L + ε) / ζ)) := by
    have h₀ : Tendsto (fun l => 2 * H * F (φ l) (lo (φ l))) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hext.2.2.1
    simpa only [zero_add, add_zero, Function.comp_apply, err, A] using
      ((((h₀.add hL).add (hε.comp hφ)).add (hΔ.comp hφ)).add (hωN.comp hφ)).div_const ζ
  have hBound (l : ℕ) : g l ≤ 1 :=
    (welfareRatio_bounds (φ l) (V (φ l)) (E (φ l)) (hseq.1 (φ l)).le
      (hseq.2.1 (φ l)) (hseq.2.2 (φ l)) hH.le (hA1 (φ l))).2
  have hLo : ∀ᶠ l in atTop, lo (φ l) ≤ 2 * H := by
    filter_upwards [hφ.eventually (hωL.eventually (eventually_le_nhds hH)),
      hφ.eventually (eventually_gt_atTop (0 : ℕ)),
      hext.2.2.1.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with l hw hk hlt
    let k := φ l
    let : ∀ i, IsProbabilityMeasure (marginalBid (V k) (E k) i) :=
      marginalBid_probability (hseq.2.1 k) (hseq.2.2 k)
    by_contra! hh
    have hAll : ∀ᵐ β ∂Measure.pi (marginalBid (V k) (E k)), numAbove (lo k) β < k := by
      filter_upwards [ae_bid_profile_bounds (hseq.2.1 k) (hseq.2.2 k) (hA1 k) (hOver k)] with β hβ
      have hzero : (Finset.univ.filter fun i => lo k < β i) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _
        exact not_lt_of_ge ((hβ i).2.trans (by linarith))
      simpa [numAbove, hzero] using hk
    have hMeas : MeasurableSet {β : Fin (n k) → ℝ | numAbove (lo k) β < k} := by
      convert measurableSet_lt (measurable_bidCount (n := n k) Finset.univ (lo k))
        (measurable_const (a := (k : ℝ))) using 1
      simp only [bidCount_eq_card, numAbove, Nat.cast_lt]
    have hFull := (ae_mem_iff_measure_eq hMeas.nullMeasurableSet).1 hAll
    have hOne : F k (lo k) = 1 := by
      unfold F kthBidCDF Measure.real
      rw [hFull, measure_univ, ENNReal.toReal_one]
    exact (ne_of_lt hlt) hOne
  have hFg : (fun l => F (φ l) (hi (φ l)) - err l) ≤ᶠ[atTop] g := by
    filter_upwards [hLo, hφ.eventually (eventually_gt_atTop (0 : ℕ))] with l hl hk
    let k := φ l
    let : ∀ i, IsProbabilityMeasure (marginalBid (V k) (E k) i) :=
      marginalBid_probability (hseq.2.1 k) (hseq.2.2 k)
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hOpt := optimal_welfare_lower k (V k) (hseq.1 k).le (hseq.2.1 k) hH (hA1 k)
    have hOpt0 : 0 < optWelfare k (V k) := (mul_pos hk' hζ).trans_le hOpt
    have hFix := fixed_auction_welfare_lower k hk (hseq.1 k).le hH.le (hω k).le
      (show 0 < Δ k by dsimp [Δ]; positivity) (hext.2.1 k).1 (hext.2.1 k).2
      (hseq.2.1 k) (hseq.2.2 k) (hA1 k) (hOver k) (hBNE k)
    have hF0 : 0 ≤ F k (lo k) := measureReal_nonneg
    have hε0 : 0 ≤ εs k := approxBNE_error_nonneg k ⟨0, hk.trans (hseq.1 k)⟩
      (hseq.2.1 k) (hseq.2.2 k) (hBNE k)
    let M := 2 * H * F k (lo k) + A l + εs k + Δ k + (n k : ℝ) * ω k / k
    have hM : 0 ≤ M := by
      have hA0 : 0 ≤ A l := (cdf_area_bounds k (V k) (E k) (hext.2.1 k).2).1
      have hΔ0 : 0 ≤ Δ k := by dsimp [Δ]; positivity
      dsimp [M]
      exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (by positivity) hF0) hA0) hε0) hΔ0)
        (div_nonneg (mul_nonneg (by positivity) (hω k).le) hk'.le)
    have hCost : (n k : ℝ) * ω k +
        (k : ℝ) * (lo k * F k (lo k) + A l + εs k + Δ k) ≤ (k : ℝ) * M := by
      have hMul := mul_le_mul_of_nonneg_right hl hF0
      have hRewrite : (k : ℝ) * ((n k : ℝ) * ω k / k) = (n k : ℝ) * ω k := by
        field_simp
      dsimp only [M]
      simp only [mul_add, hRewrite]
      linarith [mul_le_mul_of_nonneg_left hMul hk'.le]
    have hDiv : (k : ℝ) * M ≤ (M / ζ) * optWelfare k (V k) := by
      have he : (M / ζ) * ((k : ℝ) * ζ) = (k : ℝ) * M := by field_simp
      rw [← he]
      exact mul_le_mul_of_nonneg_left hOpt (div_nonneg hM hζ.le)
    have hFinal := hCost.trans hDiv
    change F k (hi k) - M / ζ ≤ welfare k (V k) (E k) / optWelfare k (V k)
    apply (le_div_iff₀ hOpt0).2
    rw [sub_mul]
    change F k (hi k) * optWelfare k (V k) ≤
      welfare k (V k) (E k) + (n k : ℝ) * ω k +
      (k : ℝ) * (lo k * F k (lo k) + A l + εs k + Δ k) at hFix
    linarith
  have hLim := liminf_lower_of_eventual_bound _ g _ (hext.2.2.2.sub hErr) hFg hBound
  change 1 - c / ζ - ε / ζ ≤ liminf g atTop
  calc
    _ ≤ 1 - (L + ε) / ζ := by rw [add_div]; linarith [div_le_div_of_nonneg_right hLc hζ.le]
    _ ≤ _ := hLim


end Theorem1

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Corollary1

theorem solution (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ)
    (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
    (εs : ℕ → ℝ)
    (hseq : IsAuctionSequence n V E) (hA1 : ∀ k, Assumption1 H κ (V k))
    (hBNE : ∀ k, IsApproxBNE k (V k) (E k) (εs k))
    (hA3 : Assumption3 n V E) (hA4 : ∀ k, IsAtomless (V k) (E k))
    (hε : Tendsto εs atTop (𝓝 0)) :
    Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop = 1 := by
  have hBounds (k : ℕ) := welfareRatio_bounds k (V k) (E k) (hseq.1 k).le
    (hseq.2.1 k) (hseq.2.2 k) hH.le (hA1 k)
  apply liminf_eq_one_of_subseq_bounds _ (fun k => (hBounds k).1) (fun k => (hBounds k).2)
  intro s hs c hc
  obtain ⟨ζ, hζ, hW⟩ := Theorem1.solution H κ hH hκ
  obtain ⟨lo, hi, θ, hθ, hext, L, hL, hsmall⟩ :=
    Lemma5.solution H κ hH hκ n V E εs hseq hA1 hBNE hA3 hA4 hε s hs (c * ζ) (mul_pos hc hζ)
  let φ := s ∘ θ
  let area (l : ℕ) := ∫ b in lo (φ l)..hi (φ l), kthBidCDF (φ l) (V (φ l)) (E (φ l)) b
  have hArea : ∀ᶠ l in atTop, area l ∈ Icc (0 : ℝ) (c * ζ) := by
    filter_upwards [hL.eventually (eventually_le_nhds hsmall)] with l hl
    let k := φ l
    let : ∀ i, IsProbabilityMeasure (marginalBid (V k) (E k) i) :=
      marginalBid_probability (hseq.2.1 k) (hseq.2.2 k)
    have h := cdf_area_bounds k (V k) (E k) (hext.2.1 k).2
    exact ⟨h.1, h.2.trans hl⟩
  obtain ⟨M, hM, ρ, hρ, hLim⟩ := isCompact_Icc.tendsto_subseq' hArea.frequently
  have hNew : IsExtremizing n V E lo hi (s ∘ (θ ∘ ρ)) :=
    ⟨hext.1.comp hρ, hext.2.1, hext.2.2.1.comp hρ.tendsto_atTop,
      hext.2.2.2.comp hρ.tendsto_atTop⟩
  refine ⟨θ ∘ ρ, hθ.comp hρ, ?_⟩
  have h := hW n V E εs 0 hseq hA1 hBNE hA3 hε (c * ζ) (mul_nonneg hc.le hζ.le)
    lo hi (s ∘ (θ ∘ ρ)) hNew ⟨M, hLim, hM.2⟩
  rw [mul_div_cancel_right₀ c hζ.ne', zero_div, sub_zero] at h
  exact h


end Corollary1

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

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

namespace Lemma6

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
  obtain ⟨ζ, hζ, hW⟩ := Theorem1.solution H κ hH hκ
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


end Lemma6

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open LargeSupplyFPA.Asymptotic MultiUnitPoA

set_option autoImplicit false

private theorem smoothing_budget (n : ℕ → ℕ) (hn : ∀ k, k < n k) :
    ∃ ω : ℕ → ℝ, (∀ k, 0 < ω k) ∧ Tendsto ω atTop (𝓝 0) ∧
      (ω =o[atTop] fun k => (k : ℝ) / (n k : ℝ)) := by
  let ω : ℕ → ℝ := fun k => 1 / ((n k : ℝ) + 1)
  have hn0 (k : ℕ) : 0 ≤ (n k : ℝ) := by positivity
  have hw (k : ℕ) : 0 < ω k := by
    dsimp [ω]
    positivity
  have hnTop : Tendsto (fun k : ℕ => n k) atTop atTop :=
    tendsto_atTop_mono (fun k => (hn k).le) tendsto_id
  have hwTop : Tendsto ω atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hnTop
  refine ⟨ω, hw, hwTop, ?_⟩
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    intro h
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hnR : (0 : ℝ) < n k := by exact_mod_cast (Nat.zero_lt_of_lt (hn k))
    exact ((div_pos hkR hnR).ne' h).elim
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_ ?_
    · exact Filter.Eventually.of_forall fun k => by
        dsimp [ω]
        positivity
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hnR : (0 : ℝ) < n k := by exact_mod_cast (Nat.zero_lt_of_lt (hn k))
      dsimp [ω]
      rw [div_div_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hkR.le
      rw [div_mul_eq_mul_div, one_mul]
      exact (div_le_one (show 0 < (n k : ℝ) + 1 by positivity)).2 (by linarith)

theorem solution (H κ : ℝ) (hH : 0 < H) (hκ : 0 < κ) :
    ∃ ζ : ℝ, 0 < ζ ∧
      ∀ (n : ℕ → ℕ) (V : ∀ k, Fin (n k) → Measure ℝ) (E : ∀ k, Fin (n k) → Kernel ℝ ℝ)
        (εs : ℕ → ℝ) (ε : ℝ),
        IsAuctionSequence n V E →
        (∀ k, Assumption1 H κ (V k)) →
        (∀ k, IsApproxBNE k (V k) (E k) (εs k)) →
        (∀ k, NoOverbidding (V k) (E k)) →
        Tendsto εs atTop (𝓝 ε) →
        (ε = 0 → Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop = 1) ∧
        (ε ∈ Set.Ioo 0 H →
          1 - ζ * ε * (1 + Real.log (H / ε)) ≤
            Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop) := by
  classical
  obtain ⟨ζ, hζ, hApprox⟩ := Lemma6.solution H κ hH hκ
  refine ⟨ζ, hζ, ?_⟩
  intro n V E εs ε hseq hA1 hBNE hNoOver hε
  obtain ⟨ω, hω, hωlim, hωsmall⟩ := smoothing_budget n hseq.1
  have hVal (k : ℕ) (i : Fin (n k)) (v : ℝ) (hv : v ∈ (V k i).support) : 0 ≤ v :=
    (Measure.support_subset_of_isClosed isClosed_Icc
      (ae_value_mem_Icc (hseq.2.1 k) (hA1 k) i) hv).1
  have hsmooth (k : ℕ) := Theorem3Nonnegative.solution k (V k) (E k) (εs k)
    (hseq.2.1 k) (hseq.2.2 k) (hBNE k) (hVal k) (ω k) (hω k)
  choose Et hStrategy hBNEt hA4t hWelfare hShift using hsmooth
  have hseqt : IsAuctionSequence n V Et := ⟨hseq.1, hseq.2.1, hStrategy⟩
  have hA3t : Assumption3 n V Et := by
    refine ⟨ω, hω, hωsmall, ?_⟩
    intro k i v hv
    exact hShift k i v v (hNoOver k i v hv)
  have hεt : Tendsto (fun k => εs k + ω k) atTop (𝓝 ε) := by
    simpa only [add_zero] using hε.add hωlim
  have hRatio : Filter.liminf (fun k => welfareRatio k (V k) (E k)) atTop =
      Filter.liminf (fun k => welfareRatio k (V k) (Et k)) atTop := by
    apply liminf_congr
    exact Filter.Eventually.of_forall fun k => by
      unfold welfareRatio
      rw [hWelfare k]
  rw [hRatio]
  refine ⟨?_, ?_⟩
  · intro he
    exact Corollary1.solution H κ hH hκ n V Et _ hseqt hA1 hBNEt hA3t hA4t (he ▸ hεt)
  · intro he
    exact hApprox n V Et _ ε hseqt hA1 hBNEt hA3t hA4t hεt he

#print axioms solution
