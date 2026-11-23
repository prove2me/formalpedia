-- Prove2me | solution 2 for LargeSupplyFPA.Asymptotic.theorem_3_nonnegative_values
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:46:49.177882+00:00
-- url     : https://prove2.me/submissions/9b355658-5b4c-464e-8dae-322e58a406a1

import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions
import Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
import Definitions.Def_LargeSupplyFPA_Asymptotic_Smoothing
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Theorems.Thm_LargeSupplyFPA_Asymptotic_lemma_7

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


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} (B : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (B j)]


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Topology Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable [∀ j, IsProbabilityMeasure (marginalBid V E j)]


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


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Set
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false

namespace MultiUnitPoA


theorem tieShare_nonneg {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) (β : Fin n → ℝ) :
    0 ≤ tieShare k i b β := by
  unfold tieShare
  exact le_min (div_nonneg (le_max_right _ _) (by positivity)) zero_le_one

theorem tieShare_le_one {n : ℕ} (k : ℕ) (i : Fin n) (b : ℝ) (β : Fin n → ℝ) :
    tieShare k i b β ≤ 1 := min_le_right _ _


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


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MultiUnitPoA

variable {n : ℕ} {V : Fin n → Measure ℝ} {E : Fin n → Kernel ℝ ℝ}
variable {ω : ℝ} {s : ℝ → ℝ}
variable [∀ i, IsProbabilityMeasure (marginalBid V E i)]


end MultiUnitPoA

open MeasureTheory ProbabilityTheory Filter Set
open LargeSupplyFPA.Asymptotic

set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace MultiUnitPoA


theorem smoothing_average_alloc {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) {ω : ℝ} {s : ℝ → ℝ}
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hs : IsSmoothingWeights V E ω s)
    (i : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    alloc k V E i b = ∫ t, smoothedAlloc k V E s i (smoothBid V E s b t) ∂jitter := by
  have hsum : 0 ≤ ∑' p : atomSet V E, s p := tsum_nonneg fun p => (hs.1 p.1 p.2).le
  have hω : 0 < ω := lt_of_le_of_lt hsum hs.2.2
  obtain ⟨h₁, h₂⟩ := LargeSupplyFPA.Asymptotic.lemma_7 k V E hV hE ω hω s hs i b hb
  by_cases hp : b ∈ atomSet V E
  · rw [h₂ hp]
    simp only [smoothBid, if_pos hp, jitter]
  · rw [h₁ hp]
    simp [smoothBid, hp]

end MultiUnitPoA

open MeasureTheory ProbabilityTheory
open LargeSupplyFPA.Asymptotic
open scoped BigOperators

set_option autoImplicit false


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


namespace Fact3


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
  have hnn : ∀ᵐ b ∂E i v, 0 ≤ b := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using (hE i).2 v
  exact hnn.mono fun b hb0 => smoothing_average_alloc k V E hV hE hs i b hb0

private theorem smoothStrategy_utility_bound (hs : IsSmoothingWeights V E ω s)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hω : 0 ≤ ω) (k : ℕ) (i : Fin n) (v : ℝ)
    (hI : Integrable (utility k V E i v) (E i v)) :
    Integrable (utility k V (smoothStrategy hs) i v) (smoothStrategy hs i v) ∧
      (∫ b, utility k V E i v b ∂E i v) - ω ≤
        ∫ d, utility k V (smoothStrategy hs) i v d ∂smoothStrategy hs i v := by
  let := (hE i).1
  let μ := E i v
  have hnn : ∀ᵐ b ∂E i v, 0 ≤ b := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio] using (hE i).2 v
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
    · have hEq (b : ℝ) (hb0 : 0 ≤ b) :
          (∫ t, ‖|v - b| * a (b, t)‖ ∂jitter) = |utility k V E i v b| := by
        have hPoint (t : ℝ) : ‖|v - b| * a (b, t)‖ = |v - b| * a (b, t) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg (b, t))]
        simp_rw [hPoint]
        rw [integral_const_mul]
        change |v - b| * (∫ t, smoothedAlloc k V E s i (smoothBid V E s b t) ∂jitter) = _
        rw [← smoothing_average_alloc k V E hV hE hs i b hb0, utility, abs_mul,
          abs_of_nonneg (alloc_nonneg k i b)]
      exact hI.abs.congr (hnn.mono fun b hb0 => (hEq b hb0).symm)
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
  filter_upwards [hnn] with b hb0
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
    rwa [← smoothing_average_alloc k V E hV hE hs i b hb0] at hb
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


theorem solution {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) (ε : ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hBNE : IsApproxBNE k V E ε)
    (hValue : ∀ i, ∀ v ∈ (V i).support, 0 ≤ v) (ω : ℝ) (hω : 0 < ω) :
    ∃ Et : Fin n → Kernel ℝ ℝ, IsStrategyProfile Et ∧
      IsApproxBNE k V Et (ε + ω) ∧
      IsAtomless V Et ∧ welfare k V E = welfare k V Et ∧
      (∀ i v t, E i v (Iic t) = 1 → Et i v (Iic (t + ω)) = 1) :=
  smoothing_with_nonnegative_values k V E ε hV hE hBNE hValue ω hω

#print axioms solution
