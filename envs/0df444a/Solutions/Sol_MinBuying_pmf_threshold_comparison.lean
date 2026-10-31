-- Prove2me | solution 1 for MinBuying.pmf_threshold_comparison
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:09:42.520092+00:00
-- url     : https://prove2.me/submissions/b569f0f0-6599-42db-99a9-c5c729c0a5b5

import Theorems.Thm_MinBuying_pmf_order_statistics
import Theorems.Thm_MinBuying_affiliated_coordinate_threshold

open MeasureTheory Set MinBuying
open scoped BigOperators
noncomputable section

private def sorted {n : ℕ} (v : Valuations n) : Valuations n := v ∘ Tuple.sort v

private lemma sorted_card {n : ℕ} (v : Valuations n) (a : ℝ) :
    (Finset.univ.filter (fun j => sorted v j < a)).card =
      (Finset.univ.filter (fun j => v j < a)).card := by
  classical
  apply Finset.card_bij (fun j _ => Tuple.sort v j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro j _ k _ hjk
    exact (Tuple.sort v).injective hjk
  · intro j hj
    refine ⟨(Tuple.sort v).symm j, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [sorted] using (Finset.mem_filter.mp hj).2

private lemma sorted_measurable (n : ℕ) : Measurable (sorted (n := n)) := by
  classical
  apply measurable_pi_lambda
  intro j
  apply measurable_of_Iio
  intro a
  have hf : Measurable (fun v : Valuations n => Finset.univ.filter (fun i => v i < a)) := by
    apply measurable_finset_iff.mpr
    intro i
    apply measurableSet_setOfPred.mp
    simpa using (measurableSet_lt (measurable_pi_apply i) measurable_const)
  have hc : Measurable (fun v : Valuations n => (Finset.univ.filter (fun i => v i < a)).card) :=
    (measurable_of_countable Finset.card).comp hf
  have he : (fun v : Valuations n => sorted v j) ⁻¹' Iio a =
      {v | j.val < (Finset.univ.filter (fun i => v i < a)).card} := by
    ext v
    change (v ∘ Tuple.sort v) j < a ↔ j.val < _
    rw [← Tuple.lt_card_lt_iff_apply_lt_of_monotone (Tuple.monotone_sort v)]
    change j.val < (Finset.univ.filter (fun i => sorted v i < a)).card ↔ _
    rw [sorted_card]
  rw [he]
  exact measurableSet_lt measurable_const hc

private lemma max_measurable (n : ℕ) (t : ℝ) : MeasurableSet (upperMaximumEvent (n := n) t) := by
  simp only [upperMaximumEvent,setOf_exists]
  exact MeasurableSet.iUnion (fun j => measurableSet_le measurable_const (measurable_pi_apply j))

private lemma event_measurable {n : ℕ} (i : Fin n) (a t : ℝ) :
    MeasurableSet (coordinateBelowAndUpperMaximumEvent i a t) :=
  (measurableSet_lt (measurable_pi_apply i) measurable_const).inter (max_measurable n t)

private lemma max_permute {n : ℕ} (v : Valuations n) (σ : Equiv.Perm (Fin n)) (t : ℝ) :
    (v ∘ σ) ∈ upperMaximumEvent t ↔ v ∈ upperMaximumEvent t := by
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨σ j,hj⟩
  · rintro ⟨j,hj⟩
    exact ⟨σ.symm j,by simpa using hj⟩

private lemma sorted_valid {n : ℕ} (μ : JointLaw n) (hμ : ValidLaw μ) :
    ValidLaw (Measure.map sorted μ) := by
  letI : IsProbabilityMeasure μ := hμ.1
  constructor
  · exact Measure.isProbabilityMeasure_map (sorted_measurable n).aemeasurable
  · have hN : MeasurableSet {v : Valuations n | ∀ i, 0 ≤ v i} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
    apply (ae_map_iff (sorted_measurable n).aemeasurable hN).mpr
    filter_upwards [hμ.2] with v hv
    exact fun i => hv (Tuple.sort v i)

private lemma sorted_ordered {n : ℕ} (μ : JointLaw n) :
    ∀ᵐ v ∂Measure.map sorted μ, Monotone v := by
  have hm : MeasurableSet {v : Valuations n | Monotone v} := by
    change MeasurableSet {v : Valuations n | ∀ i j, i ≤ j → v i ≤ v j}
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      MeasurableSet.iInter (fun _ => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))))
  apply (ae_map_iff (sorted_measurable n).aemeasurable hm).mpr
  exact ae_of_all _ (fun v => Tuple.monotone_sort v)

private lemma exchangeable_events {n : ℕ} (μ : JointLaw n) (hex : Exchangeable μ)
    (i j : Fin n) (a t : ℝ) :
    μ (coordinateBelowAndUpperMaximumEvent i a t) =
      μ (coordinateBelowAndUpperMaximumEvent j a t) := by
  let σ := Equiv.swap i j
  have hm : Measurable (permuteCoordinates σ) := by
    apply measurable_pi_lambda
    intro k
    exact measurable_pi_apply (σ k)
  have he : (permuteCoordinates σ) ⁻¹' coordinateBelowAndUpperMaximumEvent i a t =
      coordinateBelowAndUpperMaximumEvent j a t := by
    ext v
    change v (σ i) < a ∧ (v ∘ σ) ∈ upperMaximumEvent t ↔ _
    rw [max_permute]
    simp [σ,coordinateBelowAndUpperMaximumEvent]
  have hh := congrArg (fun m => m (coordinateBelowAndUpperMaximumEvent i a t)) (hex σ)
  rw [Measure.map_apply hm (event_measurable i a t),he] at hh
  exact hh.symm

private lemma sum_events_sort {n : ℕ} (μ : JointLaw n) [IsFiniteMeasure μ] (a t : ℝ) :
    ∑ i : Fin n, (μ (coordinateBelowAndUpperMaximumEvent i a t)).toReal =
      ∑ i : Fin n, ((Measure.map sorted μ) (coordinateBelowAndUpperMaximumEvent i a t)).toReal := by
  classical
  let E := fun i : Fin n => coordinateBelowAndUpperMaximumEvent i a t
  have hE (i : Fin n) : MeasurableSet (E i) := event_measurable i a t
  have hpE (i : Fin n) : MeasurableSet (sorted ⁻¹' E i) := (sorted_measurable n) (hE i)
  have hsum (v : Valuations n) :
      ∑ i : Fin n, (E i).indicator (fun _ => (1:ℝ)) v =
        ∑ i : Fin n, (sorted ⁻¹' E i).indicator (fun _ => (1:ℝ)) v := by
    have hh := Equiv.sum_comp (Tuple.sort v)
      (fun i : Fin n => (E i).indicator (fun _ => (1:ℝ)) v)
    rw [← hh]
    apply Finset.sum_congr rfl
    intro i _
    have hm := max_permute v (Tuple.sort v) t
    simp only [Set.indicator_apply, mem_preimage, E,
      coordinateBelowAndUpperMaximumEvent, mem_setOf_eq, sorted, Function.comp_apply]
    rw [hm]
  have hInt (i : Fin n) : Integrable ((E i).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const _).indicator (hE i)
  have hpInt (i : Fin n) : Integrable ((sorted ⁻¹' E i).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const _).indicator (hpE i)
  calc
    ∑ i : Fin n, (μ (E i)).toReal = ∑ i : Fin n, ∫ v, (E i).indicator (fun _ => (1:ℝ)) v ∂μ := by
      congr 1
      funext i
      exact (integral_indicator_one (hE i)).symm
    _ = ∫ v, ∑ i : Fin n, (E i).indicator (fun _ => (1:ℝ)) v ∂μ :=
      (integral_finsetSum _ (fun i _ => hInt i)).symm
    _ = ∫ v, ∑ i : Fin n, (sorted ⁻¹' E i).indicator (fun _ => (1:ℝ)) v ∂μ :=
      integral_congr_ae (ae_of_all _ hsum)
    _ = ∑ i : Fin n, ∫ v, (sorted ⁻¹' E i).indicator (fun _ => (1:ℝ)) v ∂μ :=
      integral_finsetSum _ (fun i _ => hpInt i)
    _ = ∑ i : Fin n, ((Measure.map sorted μ) (E i)).toReal := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator_const 1 (hpE i),Measure.map_apply (sorted_measurable n) (hE i)]
      simp [Measure.real]

private lemma max_sort {n : ℕ} (μ : JointLaw n) (t : ℝ) :
    (Measure.map sorted μ) (upperMaximumEvent t) = μ (upperMaximumEvent t) := by
  rw [Measure.map_apply (sorted_measurable n) (max_measurable n t)]
  congr 1
  ext v
  exact max_permute v (Tuple.sort v) t

private lemma ordered_max {n : ℕ} (hn : 0 < n) (v : Valuations n) (hv : Monotone v)
    (t : ℝ) : v ∈ upperMaximumEvent t ↔ t ≤ v ⟨n-1,by omega⟩ := by
  constructor
  · rintro ⟨i,hi⟩
    exact hi.trans (hv (show i ≤ ⟨n-1,by omega⟩ by change i.val ≤ n-1; omega))
  · intro ht
    exact ⟨_,ht⟩

theorem solution (n : ℕ) (hn : 0 < n) (w : PMF (Valuations n))
    (hμ : ValidLaw w.toMeasure) (hex : Exchangeable w.toMeasure)
    (hmtp : MTP2 (fun v => (w v).toReal)) (i : Fin n) (a b : ℝ) (hab : a ≤ b)
    (hb : 0 < w.toMeasure (upperMaximumEvent b)) :
    (w.toMeasure (coordinateBelowAndUpperMaximumEvent i a b)).toReal /
        (w.toMeasure (upperMaximumEvent b)).toReal ≤
      (w.toMeasure (coordinateBelowAndUpperMaximumEvent i a a)).toReal /
        (w.toMeasure (upperMaximumEvent a)).toReal := by
  classical
  let μ : JointLaw n := w.toMeasure
  letI : IsProbabilityMeasure μ := hμ.1
  let ν := Measure.map (sorted (n := n)) μ
  have hν : ValidLaw ν := sorted_valid μ hμ
  have hνA : Affiliated ν := by
    apply Or.inr
    refine ⟨w.map sorted, ?_, ?_⟩
    · exact PMF.toMeasure_map sorted w (sorted_measurable n)
    · exact pmf_order_statistics n w hex hmtp
  let k : Fin n := ⟨n-1,by omega⟩
  have hmax (t : ℝ) : ν {v | t ≤ v k} = μ (upperMaximumEvent t) := by
    rw [← max_sort μ t]
    apply measure_congr
    filter_upwards [sorted_ordered μ] with v hv
    exact propext (ordered_max hn v hv t).symm
  have hcoord (j : Fin n) (t : ℝ) : ν {v | v j < a ∧ t ≤ v k} =
      ν (coordinateBelowAndUpperMaximumEvent j a t) := by
    apply measure_congr
    filter_upwards [sorted_ordered μ] with v hv
    exact propext (and_congr_right (fun _ => (ordered_max hn v hv t).symm))
  have hc (j : Fin n) :
      (ν (coordinateBelowAndUpperMaximumEvent j a b)).toReal * (μ (upperMaximumEvent a)).toReal ≤
        (ν (coordinateBelowAndUpperMaximumEvent j a a)).toReal * (μ (upperMaximumEvent b)).toReal := by
    have hh := affiliated_coordinate_threshold n ν hν hνA j k a a b hab
    simpa only [hcoord,hmax] using hh
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hc j)
  rw [← Finset.sum_mul,← Finset.sum_mul,← sum_events_sort μ a b,← sum_events_sort μ a a] at hsum
  have hsame (t : ℝ) : (∑ j : Fin n, (μ (coordinateBelowAndUpperMaximumEvent j a t)).toReal) =
      (n:ℝ)*(μ (coordinateBelowAndUpperMaximumEvent i a t)).toReal := by
    simp_rw [exchangeable_events μ hex _ i a t]
    simp
  rw [hsame b,hsame a] at hsum
  have hnp : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hcross : (μ (coordinateBelowAndUpperMaximumEvent i a b)).toReal * (μ (upperMaximumEvent a)).toReal ≤
      (μ (coordinateBelowAndUpperMaximumEvent i a a)).toReal * (μ (upperMaximumEvent b)).toReal := by
    nlinarith
  have hba : upperMaximumEvent (n := n) b ⊆ upperMaximumEvent a := by
    rintro v ⟨j,hj⟩
    exact ⟨j,hab.trans hj⟩
  have ha : 0 < μ (upperMaximumEvent a) := hb.trans_le (measure_mono hba)
  have hbr : 0 < (μ (upperMaximumEvent b)).toReal := ENNReal.toReal_pos hb.ne' (measure_ne_top _ _)
  have har : 0 < (μ (upperMaximumEvent a)).toReal := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  exact (div_le_div_iff₀ hbr har).mpr hcross
