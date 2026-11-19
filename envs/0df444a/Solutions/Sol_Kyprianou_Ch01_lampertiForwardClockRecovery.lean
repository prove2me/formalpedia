-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardClockRecovery
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:30:52.127028+00:00
-- url     : https://prove2.me/submissions/251787d2-f0eb-4b56-b8f0-34283530c878

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_branchingForwardRecoveryPathwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ≥0 → Ω → ℕ)
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun s : ℝ≥0 => Y s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (Y t ω)))
    (hlocalint : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ))
    (hpositive : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < populationExtinction Y ω →
        0 < Y t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < populationExtinction Y ω →
      branchingToPoisson Y
          (Real.toNNReal (branchingOccupation Y t ω)) ω = Y t ω := by
  filter_upwards [hlocalint, hpositive] with ω hi hp
  exact Kyprianou.Ch01.branchingForwardRecoveryPathwise Y ω hi hp
