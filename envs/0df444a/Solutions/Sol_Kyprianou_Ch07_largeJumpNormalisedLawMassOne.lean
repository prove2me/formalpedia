-- Prove2me | solution 1 for Kyprianou.Ch07.largeJumpNormalisedLawMassOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:02:56.345687+00:00
-- url     : https://prove2.me/submissions/b3ee7f8d-b255-4cc6-9818-0fd51dd6acb6

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (PiH : Measure Real)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real))) :
    (Kyprianou.Ch07.largeJumpNormalisedLaw PiH) Set.univ = 1 := by
  let c : ENNReal := PiH (Set.Ioi (1 : Real))
  have hc0 : c ≠ 0 := ne_of_gt hLargePositive
  have hcTop : c ≠ ⊤ := ne_of_lt hLargeFinite
  have hmass : (PiH.restrict (Set.Ioi (1 : Real))) Set.univ = c := by
    simp [c]
  have hcInv : c⁻¹ * c = 1 := by
    rw [mul_comm]
    exact ENNReal.mul_inv_cancel hc0 hcTop
  change ((PiH.restrict (Set.Ioi (1 : Real))).withDensity
    (fun _ : Real => c⁻¹)) Set.univ = 1
  rw [MeasureTheory.withDensity_const]
  simpa [Measure.smul_apply, hmass] using hcInv
