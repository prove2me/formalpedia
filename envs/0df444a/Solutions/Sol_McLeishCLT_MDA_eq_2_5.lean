-- Prove2me | solution 1 for McLeishCLT.MDA.eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:07:41.136709+00:00
-- url     : https://prove2.me/submissions/e90a4e26-c125-4077-9fd8-d516225ee7a2

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open McLeishCLT.MDA in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hc : TendstoInMeasure P (fun n => sumSq k X n) atTop (fun _ => 1)) :
    (∀ n, P {ω | ∃ j < k n, trunc X n j ω ≠ X n j ω} ≤ P {ω | 2 < sumSq k X n ω}) ∧
      Tendsto (fun n => P {ω | 2 < sumSq k X n ω}) atTop (𝓝 0) := by
  refine ⟨fun n => ?_, ?_⟩
  · apply measure_mono
    rintro ω ⟨j, hj, hne⟩
    simp only [Set.mem_setOf_eq]
    have h2 : ¬ (∑ i ∈ Finset.range j, X n i ω ^ 2 ≤ 2) := by
      intro h
      apply hne
      unfold trunc
      rw [if_pos h, mul_one]
    have hle : ∑ i ∈ Finset.range j, X n i ω ^ 2 ≤ sumSq k X n ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hj.le)
        (fun i _ _ => sq_nonneg _)
    linarith [not_le.mp h2]
  · have h1 := hc 1 one_pos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun n => zero_le) (fun n => measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [edist_dist, ENNReal.one_le_ofReal, Real.dist_eq]
    rw [abs_of_pos (by linarith)]
    linarith
