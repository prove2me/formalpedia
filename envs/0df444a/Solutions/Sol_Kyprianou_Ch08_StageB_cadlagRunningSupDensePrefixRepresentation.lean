-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.cadlagRunningSupDensePrefixRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:36:31.431831+00:00
-- url     : https://prove2.me/submissions/a48685c0-3e53-40c6-8021-d5de8233dccc

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_runningSup_path_structure_of_cadlag
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : IsCadlag (fun t => X t ω)) (hX0 : X 0 ω = 0)
    (S : Set ℝ≥0) (hDense : Dense S) (hzero : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0) :
    runningSup X t ω =
      max (⨆ u : {u : ℝ≥0 // u ∈ S ∧ u ≤ t}, X u.1 ω)
        (X t ω) := by
  have hBound : BddAbove
      (Set.range (fun u : Set.Icc (0 : ℝ≥0) t => X u.1 ω)) := by
    refine (Kyprianou.Ch01.cadlag_runningSup_bddAbove
      (fun u => X u ω) hc t).mono ?_
    rintro z ⟨u, rfl⟩
    exact ⟨u.1, u.2.2, rfl⟩
  calc
    runningSup X t ω =
        ⨆ u : Set.Icc (0 : ℝ≥0) t, X u.1 ω :=
          (Kyprianou.Ch08.StageB.runningSup_path_structure_of_cadlag
            X ω hc hX0).2.2 t
    _ = max (⨆ u : {u : ℝ≥0 // u ∈ S ∧ u ≤ t}, X u.1 ω)
          (X t ω) :=
      AvramDividend.Classical.dense_timeSup_with_endpoint
        (fun u => X u ω) (fun u => (hc u).1)
        S hDense hzero t hBound
