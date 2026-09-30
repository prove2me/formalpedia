-- Prove2me | solution 1 for Martingale.clt_truncation_matches_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T01:10:15.106062+00:00
-- url     : https://prove2.me/submissions/f0dd1b91-a4df-4800-b714-643444971612

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

open MeasureTheory Filter
open scoped ENNReal Topology

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (D : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n k, Measurable (D n k))
    (σ : ℝ) (hσ2 : σ ^ 2 < 2)
    (hvar : TendstoInMeasure P
      (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω ^ 2) atTop (fun _ => σ ^ 2)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (∑ k ∈ Finset.range n, D n k ω)
        - ∑ k ∈ Finset.range n, (Set.indicator
            {ω' | ∑ j ∈ Finset.range k, D n j ω' ^ 2 ≤ 2} (D n k) ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hvar ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hvar (2 - σ ^ 2) (sub_pos.mpr hσ2)) (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  by_contra hbad
  have hs : ∑ k ∈ Finset.range n, D n k ω ^ 2 ≤ 2 := by
    have habs := le_abs_self ((∑ k ∈ Finset.range n, D n k ω ^ 2) - σ ^ 2)
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hbad
    linarith
  have heq : (∑ k ∈ Finset.range n, D n k ω) =
      ∑ k ∈ Finset.range n, Set.indicator
        {ω' | ∑ j ∈ Finset.range k, D n j ω' ^ 2 ≤ 2} (D n k) ω := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Set.indicator_of_mem]
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hk)))
      (fun j _ _ => sq_nonneg (D n j ω))).trans hs
  simp only [Set.mem_setOf_eq, heq, sub_self, sub_zero, norm_zero] at hω
  exact (not_le_of_gt hε) hω

#print axioms solution
