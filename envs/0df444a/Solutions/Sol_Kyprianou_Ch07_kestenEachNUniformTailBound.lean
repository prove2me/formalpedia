-- Prove2me | solution 1 for Kyprianou.Ch07.kestenEachNUniformTailBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:54:29.395196+00:00
-- url     : https://prove2.me/submissions/3930370a-534d-4728-a917-5db3ccaee366

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
    (hConvolutionAsymptotics : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ n : Nat, 1 ≤ n →
      ∃ C : Real, 0 < C ∧ ∀ x : Real, 0 < x →
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal ≤ C := by
  intro n hn
  by_cases hOne : n = 1
  · subst n
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    rw [Kyprianou.Ch07.kestenOnefoldTailRatio G hPositiveTail x hx]
  · have hTwo : 2 ≤ n := by omega
    exact Kyprianou.Ch07.kestenFixedNUniformTailBound
      G hPositiveTail n hTwo (hConvolutionAsymptotics n hTwo)
