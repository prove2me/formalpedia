-- Prove2me | solution 1 for LevyStochCalc.Probability.isIntegerValued_of_isPiSystem
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:57:22.184624+00:00
-- url     : https://prove2.me/submissions/f1be5d2e-f82c-4aaa-97e4-0771ce6d0edb

import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integer-valued finite measures

A measure is integer-valued when every measurable set carries a natural mass. On a measurable
space with a countable separating family such a measure, if finite, is a finite sum of Dirac
masses: a binary search along the separating family isolates a point of mass at least one, and
removing it lowers the total mass by at least one, so the recursion terminates.

Integrality on a generating π-system already gives integrality everywhere, since the sets of
natural mass form a Dynkin system as soon as the ambient measure is finite.
-/

namespace LevyStochCalc.Probability

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

section PiSystem



theorem _root_.solution {μ : Measure α} [IsFiniteMeasure μ] {C : Set (Set α)}
    (hgen : ‹MeasurableSpace α› = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (hC : ∀ B ∈ C, ∃ n : ℕ, μ B = n) (huniv : ∃ N : ℕ, μ Set.univ = N) :
    LevyStochCalc.Probability.IsIntegerValued μ := by
  obtain ⟨N, hN⟩ := huniv
  intro B hB
  refine MeasurableSpace.induction_on_inter (C := fun s _ => ∃ n : ℕ, μ s = n) hgen hpi
    ⟨0, by simp⟩ (fun t ht => hC t ht) ?_ ?_ B hB
  · rintro t htm ⟨n, hn⟩
    have hle : n ≤ N := by
      have : μ t ≤ μ Set.univ := measure_mono (Set.subset_univ t)
      rw [hn, hN] at this
      exact_mod_cast this
    refine ⟨N - n, ?_⟩
    rw [measure_compl htm (measure_ne_top μ t), hN, hn]
    exact (ENNReal.natCast_sub N n).symm
  · intro f hdisj hfm hf
    choose m hm using hf
    have hU : μ (⋃ i, f i) = ∑' i, (m i : ℝ≥0∞) := by
      rw [measure_iUnion hdisj hfm]; simp_rw [hm]
    have hUN : μ (⋃ i, f i) ≤ N := hN ▸ measure_mono (Set.subset_univ _)
    have hfin : {i | m i ≠ 0}.Finite := by
      by_contra hinf
      obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
      have h1 : ∑ i ∈ s, (m i : ℝ≥0∞) ≤ ∑' i, (m i : ℝ≥0∞) := ENNReal.sum_le_tsum s
      have h2 : ((N + 1 : ℕ) : ℝ≥0∞) ≤ ∑ i ∈ s, (m i : ℝ≥0∞) := by
        rw [← hcard, ← Nat.cast_sum]
        have : s.card ≤ ∑ i ∈ s, m i := by
          have := Finset.card_nsmul_le_sum s m 1 (fun i hi => Nat.one_le_iff_ne_zero.2 (hs hi))
          simpa using this
        exact_mod_cast this
      have h3 := h2.trans (h1.trans (hU ▸ hUN))
      have : N + 1 ≤ N := by exact_mod_cast h3
      omega
    refine ⟨∑ i ∈ hfin.toFinset, m i, ?_⟩
    rw [hU, tsum_eq_sum (s := hfin.toFinset), Nat.cast_sum]
    intro i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hi
    simp [hi]
