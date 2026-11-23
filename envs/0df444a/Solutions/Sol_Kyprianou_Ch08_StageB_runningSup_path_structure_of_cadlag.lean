-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.runningSup_path_structure_of_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:45:34.301003+00:00
-- url     : https://prove2.me/submissions/565a80ee-d884-41bb-8d0c-b7e04d1f233a

import Mathlib.Topology.Order.LeftRight
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08
open Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : IsCadlag fun t => X t ω) (hX0 : X 0 ω = 0) :
    Monotone (fun t : ℝ≥0 => runningSup X t ω) ∧
    (∀ t : ℝ≥0, X t ω ≤ runningSup X t ω) ∧
    (∀ T : ℝ≥0, runningSup X T ω = ⨆ u : Icc (0 : ℝ≥0) T, X u.1 ω) := by
  have hb (T : ℝ≥0) :
      BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = X s ω} :=
    Kyprianou.Ch01.cadlag_runningSup_bddAbove (fun t => X t ω) hc T
  have hn (T : ℝ≥0) :
      {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = X s ω}.Nonempty :=
    ⟨X 0 ω, 0, zero_le, rfl⟩
  constructor
  · intro s t hst
    change sSup {z : ℝ | ∃ u : ℝ≥0, u ≤ s ∧ z = X u ω} ≤
      sSup {z : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ z = X u ω}
    apply csSup_le (hn s)
    rintro z ⟨u, hu, rfl⟩
    exact le_csSup (hb t) ⟨u, hu.trans hst, rfl⟩
  constructor
  · intro t
    change X t ω ≤ sSup {z : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ z = X u ω}
    exact le_csSup (hb t) ⟨t, le_rfl, rfl⟩
  · intro T
    letI : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
    have hrange :
        Set.range (fun u : Icc (0 : ℝ≥0) T => X u.1 ω) =
          {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = X s ω} := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨u.1, u.2.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, zero_le, hs⟩, rfl⟩
    have hbr : BddAbove (Set.range
        (fun u : Icc (0 : ℝ≥0) T => X u.1 ω)) := by
      rw [hrange]
      exact hb T
    change sSup {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = X s ω} =
      ⨆ u : Icc (0 : ℝ≥0) T, X u.1 ω
    apply le_antisymm
    · apply csSup_le (hn T)
      rintro z ⟨u, hu, rfl⟩
      exact le_ciSup hbr ⟨u, zero_le, hu⟩
    · refine ciSup_le (fun u => ?_)
      exact le_csSup (hb T) ⟨u.1, u.2.2, rfl⟩
