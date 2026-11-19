-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOccupationMonotoneFromLocalIntegrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:17:11.783221+00:00
-- url     : https://prove2.me/submissions/54b47dcc-f507-4417-8cf6-05474a7e6c08

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hlocalint : ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ)) :
    Monotone (fun t : ℝ≥0 => branchingOccupation Y t ω) := by
  intro a b hab
  have hf : ∀ s : ℝ, 0 ≤ (Y (Real.toNNReal s) ω : ℝ) := by
    intro s
    exact_mod_cast Nat.zero_le (Y (Real.toNNReal s) ω)
  change (∫ s in (0 : ℝ)..(a : ℝ),
    (Y (Real.toNNReal s) ω : ℝ)) ≤
    ∫ s in (0 : ℝ)..(b : ℝ), (Y (Real.toNNReal s) ω : ℝ)
  exact intervalIntegral.integral_mono_interval
    (show (0 : ℝ) ≤ 0 by rfl)
    (show (0 : ℝ) ≤ (a : ℝ) by exact a.property)
    (by exact_mod_cast hab)
    (Filter.Eventually.of_forall hf)
    (hlocalint b)
