-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiReverseClockRecovery
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:38:46.266608+00:00
-- url     : https://prove2.me/submissions/19681e4d-4825-477c-868d-2b5324849c1f

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonReverseRecoveryPathwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℤ)
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun s : ℝ≥0 => X s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (X t ω)))
    (hlocalint : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ =>
          if 0 < X (Real.toNNReal s) ω then
            1 / (X (Real.toNNReal s) ω : ℝ)
          else 0)
        volume 0 (t : ℝ)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∀ s : ℝ≥0, s ≤ t → 0 < X s ω) →
        compoundPoissonToBranching X
          (Real.toNNReal (reciprocalOccupation X t ω).toReal) ω = X t ω := by
  filter_upwards [hcadlag, hlocalint] with ω hc hi
  exact Kyprianou.Ch01.compoundPoissonReverseRecoveryPathwise X ω hc hi
