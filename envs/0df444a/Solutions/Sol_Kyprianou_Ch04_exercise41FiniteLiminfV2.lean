-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteLiminfV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:37.88357+00:00
-- url     : https://prove2.me/submissions/82caf547-563f-46bb-9c83-fe2c9571a58e

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false


theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : C < ⊤) (hN : ∀ n, Measurable (N n))
    (hBound : ∀ n, (∫⁻ ω, N n ω ∂P) ≤ C) :
    ∀ᵐ ω ∂P, Filter.liminf (fun n => N n ω) atTop < ⊤ := by
  have hb : Filter.liminf (fun n => ∫⁻ ω, N n ω ∂P) atTop ≤ C := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    exact iSup_le fun n => (iInf₂_le n le_rfl).trans (hBound n)
  exact ae_lt_top (Measurable.liminf hN)
    (ne_of_lt ((lintegral_liminf_le hN).trans_lt (hb.trans_lt hC)))
