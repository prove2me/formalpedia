-- Prove2me | solution 1 for Kyprianou.Ch07.largeJumpNormalisedLawTailAboveOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:15:04.463562+00:00
-- url     : https://prove2.me/submissions/68ab2573-6828-43ff-a87d-4a14f50d0f66

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (PiH : Measure Real) (x : Real) (hx : 1 ≤ x) :
    (Kyprianou.Ch07.largeJumpNormalisedLaw PiH) (Set.Ioi x) =
      (PiH (Set.Ioi (1 : Real)))⁻¹ * PiH (Set.Ioi x) := by
  change ((PiH.restrict (Set.Ioi (1 : Real))).withDensity
    (fun _ : Real => (PiH (Set.Ioi (1 : Real)))⁻¹))
      (Set.Ioi x) =
        (PiH (Set.Ioi (1 : Real)))⁻¹ * PiH (Set.Ioi x)
  rw [MeasureTheory.withDensity_const]
  simp only [Measure.smul_apply]
  rw [Measure.restrict_apply measurableSet_Ioi]
  have hEq : (Set.Ioi x ∩ Set.Ioi (1 : Real)) = Set.Ioi x := by
    ext y
    constructor
    · intro hy
      exact hy.1
    · intro hy
      exact ⟨hy, lt_of_le_of_lt hx hy⟩
  rw [hEq]
  rfl
