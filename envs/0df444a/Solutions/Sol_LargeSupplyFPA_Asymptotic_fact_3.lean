-- Prove2me | solution 1 for LargeSupplyFPA.Asymptotic.fact_3
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T13:11:44.410221+00:00
-- url     : https://prove2.me/submissions/12ea1781-14ed-476d-a6de-43e40ef27c83

import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions

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

#print axioms solution
