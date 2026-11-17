-- Prove2me | solution 1 for Kyprianou.Ch07.kestenEachOrderHasFiniteTailBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:29:56.353862+00:00
-- url     : https://prove2.me/submissions/c04ad37c-b120-4993-8a8a-61c2dd5d734f

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_kestenOnefoldTailRatio
import Theorems.Thm_Kyprianou_Ch07_kestenFixedNUniformTailBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConv : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ n : Nat, 1 ≤ n →
      ∃ C : Real, 0 < C ∧
        ∀ x : Real, 0 < x →
          ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
            (G (Set.Ioi x)).toReal ≤ C := by
  intro n hn
  rcases (Nat.le_iff_lt_or_eq).mp hn with hnGt | hnEq
  · exact Kyprianou.Ch07.kestenFixedNUniformTailBound
      G hPositiveTail n hnGt (hConv n hnGt)
  · subst n
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    rw [Kyprianou.Ch07.kestenOnefoldTailRatio G hPositiveTail x hx]
