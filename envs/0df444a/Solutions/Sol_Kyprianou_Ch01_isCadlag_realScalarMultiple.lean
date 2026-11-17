-- Prove2me | solution 1 for Kyprianou.Ch01.isCadlag_realScalarMultiple
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:22:59.54809+00:00
-- url     : https://prove2.me/submissions/2a273142-7dbe-4a5e-bd30-0f2ed835320c

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open ProbabilityTheory Set Filter
open scoped NNReal
set_option autoImplicit false


theorem Kyprianou.Ch01.isCadlag_realScalarMultiple
    (c : ℝ) (f : ℝ≥0 → ℝ)
    (h : IsCadlag f) :
    IsCadlag (fun t => c * f t) := by
  intro t
  obtain ⟨h1, l, hl⟩ := h t
  exact ⟨continuousWithinAt_const.mul h1, c * l, hl.const_mul c⟩

theorem solution
    (c : ℝ) (f : ℝ≥0 → ℝ)
    (h : IsCadlag f) :
    IsCadlag (fun t => c * f t) :=
  Kyprianou.Ch01.isCadlag_realScalarMultiple c f h
