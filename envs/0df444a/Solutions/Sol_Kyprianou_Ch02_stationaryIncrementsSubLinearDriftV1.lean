-- Prove2me | solution 1 for Kyprianou.Ch02.stationaryIncrementsSubLinearDriftV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:47:25.448317+00:00
-- url     : https://prove2.me/submissions/cf3d97de-f676-483f-9221-207341e4f8c2

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (hstationary : ProbabilityTheory.HasStationaryIncrements X P) :
    ProbabilityTheory.HasStationaryIncrements
      (fun (t : ℝ≥0) ω => X t ω - (t : ℝ) * c) P := by
  intro s h
  have hlaw := (hstationary s h).sub_const ((h : ℝ) * c)
  have hleft :
      (fun ω : Ω =>
        ProbabilityTheory.increment
          (fun (t : ℝ≥0) ω => X t ω - (t : ℝ) * c) s (s + h) ω) =
      (fun ω => ProbabilityTheory.increment X s (s + h) ω - (h : ℝ) * c) := by
    funext ω
    simp only [ProbabilityTheory.increment]
    push_cast
    ring
  have hright :
      (fun ω : Ω =>
        ProbabilityTheory.increment
          (fun (t : ℝ≥0) ω => X t ω - (t : ℝ) * c) 0 h ω) =
      (fun ω => ProbabilityTheory.increment X 0 h ω - (h : ℝ) * c) := by
    funext ω
    simp only [ProbabilityTheory.increment]
    push_cast
    ring
  change ProbabilityTheory.IdentDistrib
    (fun ω : Ω => ProbabilityTheory.increment
      (fun (t : ℝ≥0) ω => X t ω - (t : ℝ) * c) s (s + h) ω)
    (fun ω : Ω => ProbabilityTheory.increment
      (fun (t : ℝ≥0) ω => X t ω - (t : ℝ) * c) 0 h ω) P P
  rw [hleft, hright]
  exact hlaw
