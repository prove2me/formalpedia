-- Prove2me | solution 1 for GreedWorks.OnlineList.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:23:39.631412+00:00
-- url     : https://prove2.me/submissions/65224579-86ed-4453-ac4c-74ba1b9c113e

import Mathlib

set_option autoImplicit false

open MeasureTheory

lemma ol_sum_range (n : ℕ) :
    ∑ r ∈ Finset.range n, ((r : ENNReal) + 1 / 2) = (n : ENNReal) ^ 2 / 2 := by
  have h2 : (2 : ENNReal) * (1 / 2) = 1 := by
    rw [mul_one_div]; exact ENNReal.div_self (by norm_num) (by norm_num)
  have key : 2 * ∑ r ∈ Finset.range n, ((r : ENNReal) + 1 / 2) = (n : ENNReal) ^ 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      calc (n : ENNReal) ^ 2 + 2 * ((n : ENNReal) + 1 / 2)
          = (n : ENNReal) ^ 2 + 2 * n + 2 * (1 / 2) := by ring
        _ = ((n : ENNReal) + 1) ^ 2 := by rw [h2]; ring
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]; exact key

lemma ol_tsum_ite (n : ℕ) (c : ℕ → ENNReal) :
    ∑' r : ℕ, (if r < n then c r else 0) = ∑ r ∈ Finset.range n, c r := by
  rw [tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro r hr
    simp at hr; simp [hr]
  · intro r hr
    simp at hr; simp [hr]

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : Ω → ℕ) (hX : Measurable X) :
    (∑' r : ℕ, Pr {ω | r < X ω}) = (∫⁻ ω, (X ω : ENNReal) ∂Pr) ∧
    (∑' r : ℕ, ((r : ENNReal) + 1 / 2) * Pr {ω | r < X ω}) =
      (1 / 2 : ENNReal) * (∫⁻ ω, ((X ω : ENNReal) ^ 2) ∂Pr) := by
  have hmeas : ∀ r : ℕ, MeasurableSet {ω | r < X ω} := fun r =>
    hX (measurableSet_Ioi (a := r))
  constructor
  · have : ∀ ω, (X ω : ENNReal) = ∑' r : ℕ, ({ω | r < X ω}.indicator (fun _ => (1 : ENNReal)) ω) := by
      intro ω
      have := ol_tsum_ite (X ω) (fun _ => 1)
      simp only [Set.indicator, Set.mem_setOf_eq]
      rw [this]; simp
    simp_rw [this]
    rw [lintegral_tsum (fun r => ((measurable_const.indicator (hmeas r))).aemeasurable)]
    congr 1; ext r
    rw [lintegral_indicator (hmeas r)]; simp
  · have : ∀ ω, (1 / 2 : ENNReal) * (X ω : ENNReal) ^ 2 =
        ∑' r : ℕ, ({ω | r < X ω}.indicator (fun _ => ((r : ENNReal) + 1 / 2)) ω) := by
      intro ω
      have := ol_tsum_ite (X ω) (fun r => (r : ENNReal) + 1 / 2)
      simp only [Set.indicator, Set.mem_setOf_eq]
      rw [this, ol_sum_range, one_div, div_eq_mul_inv, mul_comm]
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    simp_rw [this]
    rw [lintegral_tsum (fun r => ((measurable_const.indicator (hmeas r))).aemeasurable)]
    congr 1; ext r
    rw [lintegral_indicator (hmeas r)]; simp
