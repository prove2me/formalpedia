-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_dominated_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:26:25.460281+00:00
-- url     : https://prove2.me/submissions/385f09c0-df19-478c-b202-c8f7f5d493bf

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (A : Set Omega) (Q : Nat → Omega → Complex) (R : Omega → Complex) (B : Omega → Real)
    (hQ : ∀ n, Integrable (Q n) P) (hB : Integrable B P)
    (hBound : ∀ n, ∀ᵐ w ∂P, ‖Q n w‖ ≤ B w)
    (hLim : ∀ᵐ w ∂P, Tendsto (fun n => Q n w) atTop (nhds (R w)))
    (hZero : ∀ n, (∫ w in A, Q n w ∂P) = 0) :
    (∫ w in A, R w ∂P) = 0  := by
  have hle : P.restrict A ≤ P := Measure.restrict_le_self
  have hlim := tendsto_integral_of_dominated_convergence (μ := P.restrict A) B
    (fun n => ((hQ n).mono_measure hle).aestronglyMeasurable)
    (hB.mono_measure hle)
    (fun n => ae_mono hle (hBound n)) (ae_mono hle hLim)
  have hc : Tendsto (fun n => ∫ w in A, Q n w ∂P) atTop (nhds 0) := by
    simp only [hZero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hc
