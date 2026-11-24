-- Prove2me | solution 1 for Kyprianou.Ch03.delayedOpenInfValueInClosedNeighbourhoodV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:35:12.038574+00:00
-- url     : https://prove2.me/submissions/cef5edf6-8f56-4566-a11d-eabf8c46d431

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : NNReal → ℝ)
    (hrc : ∀ t : NNReal, ContinuousWithinAt f (Set.Ici t) t)
    (B : Set ℝ) (r : ℝ) (a u : NNReal)
    (hu : (u : WithTop NNReal) = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ f t ∈ Metric.thickening r B})) :
    f u ∈ Metric.cthickening r B := by
  by_contra hn
  have hc := (hrc u).eventually
    ((Metric.isClosed_cthickening : IsClosed (Metric.cthickening r B)).isOpen_compl.mem_nhds hn)
  obtain ⟨v, huv, hv⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hc
  have hs : sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ f t ∈ Metric.thickening r B}) < (v : WithTop NNReal) := by
    rw [← hu]
    exact WithTop.coe_lt_coe.mpr huv
  obtain ⟨_, ⟨t, ⟨hat, ht⟩, rfl⟩, htv⟩ := sInf_lt_iff.mp hs
  have hut : u ≤ t := WithTop.coe_le_coe.mp (hu.trans_le (sInf_le ⟨t, ⟨hat, ht⟩, rfl⟩))
  exact (hv ⟨hut, WithTop.coe_lt_coe.mp htv⟩) (Metric.thickening_subset_cthickening r B ht)
