-- Prove2me | solution 1 for KSATSingleFlip.Connect.poisson_zero_count_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:00:36.248566+00:00
-- url     : https://prove2.me/submissions/2376d4fa-b308-4022-a079-1769be8d43eb

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N) (hNlaw : Measure.map N P = poissonMeasure 0)
    (Y : Ω → ℝ) (c u : ℝ) (hu : 0 < u) (hzero : ∀ ω, N ω = 0 → Y ω = c) :
    P.real {ω | Y ω ≤ (∫ ω, Y ω ∂P)-u} = 0 := by
  have hP0 : P {ω | N ω = 0} = 1 := by
    have hh := congrArg (fun μ : Measure ℕ => μ {0}) hNlaw
    rw [Measure.map_apply hN (measurableSet_singleton 0)] at hh
    have hz : P (N ⁻¹' {0}) = 1 := by simpa [poissonMeasure_singleton] using hh
    convert hz using 1
    congr 1
  have hNae : ∀ᵐ ω ∂P, N ω = 0 := by
    apply (ae_iff_measure_eq ((measurableSet_singleton 0).preimage hN).nullMeasurableSet).2
    simpa using hP0
  have hYae : ∀ᵐ ω ∂P, Y ω = c := hNae.mono (fun ω hω => hzero ω hω)
  have hmean : (∫ ω, Y ω ∂P) = c := by
    calc
      (∫ ω, Y ω ∂P) = ∫ _ : Ω, c ∂P := integral_congr_ae hYae
      _ = c := by simp
  have hE : P {ω | Y ω ≤ (∫ ω, Y ω ∂P)-u} = 0 := by
    apply measure_mono_null _ (ae_iff.mp hYae)
    intro ω hω
    change Y ω ≠ c
    have hh : Y ω ≤ c-u := by simpa [hmean] using hω
    linarith
  simp [measureReal_def,hE]
