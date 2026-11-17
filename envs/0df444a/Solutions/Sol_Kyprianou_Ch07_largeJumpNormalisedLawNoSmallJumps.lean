-- Prove2me | solution 1 for Kyprianou.Ch07.largeJumpNormalisedLawNoSmallJumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:05:40.77581+00:00
-- url     : https://prove2.me/submissions/048c841c-7e12-4381-9072-f1cdadaf85df

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (PiH : Measure Real) :
    (Kyprianou.Ch07.largeJumpNormalisedLaw PiH)
      (Set.Iic (1 : Real)) = 0 := by
  change ((PiH.restrict (Set.Ioi (1 : Real))).withDensity
    (fun _ : Real => (PiH (Set.Ioi (1 : Real)))⁻¹))
      (Set.Iic (1 : Real)) = 0
  have hEmpty : (Set.Iic (1 : Real)) ∩ Set.Ioi 1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi,
      Set.mem_empty_iff_false, iff_false]
    intro hx
    exact (not_lt_of_ge hx.1) hx.2
  rw [MeasureTheory.withDensity_const]
  simp [hEmpty]
