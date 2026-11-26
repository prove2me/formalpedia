-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ce_binary_events_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:16:52.100073+00:00
-- url     : https://prove2.me/submissions/ccaf7b23-a72a-49ca-a15d-8cf0458c6522

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- Finite intersections of empty or universal events factor under probability measures. -/
theorem solution {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Finset ι) (A : ι → Set Ω)
    (hs : ∀ k ∈ S, A k = ∅ ∨ A k = univ) :
    P (⋂ i ∈ S, A i) = ∏ i ∈ S, P (A i) := by
  classical
  by_cases h : ∃ k ∈ S, A k = ∅
  · obtain ⟨k,hk,hk0⟩ := h
    have hz : (⋂ i ∈ S, A i) = ∅ :=
      subset_empty_iff.mp (hk0 ▸ iInter₂_subset k hk)
    rw [hz, measure_empty]
    exact (Finset.prod_eq_zero hk (by rw [hk0,measure_empty])).symm
  · have hU (k : ι) (hk : k ∈ S) : A k = univ :=
      (hs k hk).resolve_left fun he => h ⟨k,hk,he⟩
    have hI : (⋂ i ∈ S, A i) = univ := by
      ext w
      simp only [mem_iInter,mem_univ,iff_true]
      intro k hk
      rw [hU k hk]
      trivial
    rw [hI,measure_univ]
    exact (Finset.prod_eq_one fun k hk => by rw [hU k hk,measure_univ]).symm
