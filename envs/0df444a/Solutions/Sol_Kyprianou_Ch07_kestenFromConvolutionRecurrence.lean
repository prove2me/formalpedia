-- Prove2me | solution 1 for Kyprianou.Ch07.kestenFromConvolutionRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:35:13.809883+00:00
-- url     : https://prove2.me/submissions/ed8ce076-1880-4350-be93-e2012bc5d246

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_kestenGeometricRecursion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (epsilon : Real) (hEpsilon : 0 < epsilon)
    (A B : Real) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (xi : Nat → Real)
    (hBase : xi 0 ≤ B)
    (hStep : ∀ n : Nat,
      xi (n + 1) ≤ A + (1 + epsilon) * xi n)
    (hTail : ∀ n : Nat, 1 ≤ n →
      ∀ x : Real, 0 < x →
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal ≤ xi n) :
    ∃ C : Real, 0 < C ∧
      ∀ n : Nat, 1 ≤ n →
        ∀ x : Real, 0 < x →
          ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
            (G (Set.Ioi x)).toReal ≤ C * (1 + epsilon) ^ n := by
  have hDiv : 0 ≤ A / epsilon :=
    div_nonneg hA (le_of_lt hEpsilon)
  let C : Real := B + A / epsilon + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro n hn x hx
  have hRec := Kyprianou.Ch07.kestenGeometricRecursion
    epsilon A B hEpsilon xi hBase hStep n
  have hPow : 0 ≤ (1 + epsilon) ^ n :=
    pow_nonneg (by linarith) n
  have hXi : xi n ≤ (B + A / epsilon) * (1 + epsilon) ^ n :=
    le_trans (le_add_of_nonneg_right hDiv) hRec
  calc
    _ ≤ xi n := hTail n hn x hx
    _ ≤ (B + A / epsilon) * (1 + epsilon) ^ n := hXi
    _ ≤ C * (1 + epsilon) ^ n := by
      dsimp [C]
      nlinarith
