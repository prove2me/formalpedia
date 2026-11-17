-- Prove2me | solution 1 for Kyprianou.Ch07.kestenSupRatioBounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:32:47.96256+00:00
-- url     : https://prove2.me/submissions/c74530ec-e713-4e4f-87ec-c66547ecf885

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) (n : Nat) (C : Real)
    (hC : ∀ x : Real, 0 < x →
      ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
        (G (Set.Ioi x)).toReal ≤ C)
    (x : Real) (hx : 0 < x) :
    let S : Set Real := { y | ∃ z : Real, 0 < z ∧
      y = ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi z)).toReal /
        (G (Set.Ioi z)).toReal };
    ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
      (G (Set.Ioi x)).toReal ≤ sSup S ∧
      sSup S ≤ C := by
  dsimp
  let S : Set Real := { y | ∃ z : Real, 0 < z ∧
      y = ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi z)).toReal /
        (G (Set.Ioi z)).toReal }
  have hUpper : ∀ y ∈ S, y ≤ C := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hC z hz
  have hBdd : BddAbove S := ⟨C, hUpper⟩
  have hMem :
      ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
        (G (Set.Ioi x)).toReal ∈ S := ⟨x, hx, rfl⟩
  have hNonempty : S.Nonempty := ⟨_, hMem⟩
  exact ⟨le_csSup hBdd hMem, csSup_le hNonempty hUpper⟩
