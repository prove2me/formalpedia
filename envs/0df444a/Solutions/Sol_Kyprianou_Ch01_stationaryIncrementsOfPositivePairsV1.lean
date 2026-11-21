-- Prove2me | solution 1 for Kyprianou.Ch01.stationaryIncrementsOfPositivePairsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:41:21.809584+00:00
-- url     : https://prove2.me/submissions/ff818cb6-c37b-4a43-abaf-f19ced7161aa

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (T : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ s : ℝ≥0, AEMeasurable (T s) P)
    (hPositive : ∀ (s h : ℝ≥0), 0 < s → 0 < h →
      IdentDistrib (increment T s (s + h))
        (increment T 0 h) P P) :
    HasStationaryIncrements T P := by
  intro s h
  by_cases hs : s = 0
  · subst s
    have hA : AEMeasurable (increment T 0 h) P :=
      (hMeas h).sub (hMeas 0)
    simpa only [zero_add] using (IdentDistrib.refl hA)
  by_cases hh : h = 0
  · subst h
    have hEq : increment T s (s + 0) = increment T 0 0 := by
      funext ω
      simp [increment]
    rw [hEq]
    have hA : AEMeasurable (increment T 0 0) P :=
      (hMeas 0).sub (hMeas 0)
    exact IdentDistrib.refl hA
  have hsZero : (0 : ℝ≥0) ≤ s := zero_le
  have hhZero : (0 : ℝ≥0) ≤ h := zero_le
  have hsPos : 0 < s :=
    lt_of_le_of_ne hsZero (Ne.symm hs)
  have hhPos : 0 < h :=
    lt_of_le_of_ne hhZero (Ne.symm hh)
  exact hPositive s h hsPos hhPos
