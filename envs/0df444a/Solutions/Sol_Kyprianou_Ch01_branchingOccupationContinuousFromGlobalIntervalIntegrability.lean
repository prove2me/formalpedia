-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOccupationContinuousFromGlobalIntervalIntegrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:08:09.14595+00:00
-- url     : https://prove2.me/submissions/c311fa46-860a-4790-a7d6-09d4351ab3a5

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Lamperti's occupation primitive is continuous whenever its integrand
is interval-integrable on every compact real interval. -/
theorem solution
    {Ω : Type*}
    (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hglobal : ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume a b) :
    Continuous (fun t : ℝ≥0 => branchingOccupation Y t ω) := by
  have hReal : Continuous (fun t : ℝ =>
      ∫ s in (0 : ℝ)..t,
        (Y (Real.toNNReal s) ω : ℝ)) :=
    intervalIntegral.continuous_primitive hglobal 0
  change Continuous (fun t : ℝ≥0 =>
    (fun r : ℝ =>
      ∫ s in (0 : ℝ)..r,
        (Y (Real.toNNReal s) ω : ℝ)) (t : ℝ))
  exact hReal.comp NNReal.continuous_coe
