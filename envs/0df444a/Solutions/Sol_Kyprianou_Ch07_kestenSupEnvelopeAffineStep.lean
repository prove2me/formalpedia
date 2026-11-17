-- Prove2me | solution 1 for Kyprianou.Ch07.kestenSupEnvelopeAffineStep
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:43:48.843962+00:00
-- url     : https://prove2.me/submissions/953a5268-5dd4-4374-af9e-e850c65572ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
import Theorems.Thm_Kyprianou_Ch07_kestenOneBigJumpPointwise
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
        atTop (nhds (1 : Real)))
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    ∃ A : Real, 1 ≤ A ∧
      ∀ n : Nat, 1 ≤ n →
        Kyprianou.Ch07.kestenSupEnvelope G (n + 1) ≤
          A + (1 + epsilon) * Kyprianou.Ch07.kestenSupEnvelope G n := by
  obtain ⟨A, hA, hPointwise⟩ :=
    Kyprianou.Ch07.kestenOneBigJumpPointwise
      G hPositiveTail hConv epsilon hEpsilon
  refine ⟨A, hA, ?_⟩
  intro n hn
  let S : Set Real := { y | ∃ x : Real, 0 < x ∧
    y = ((Kyprianou.Ch07.convolutionPower G (n + 1))
      (Set.Ioi x)).toReal / (G (Set.Ioi x)).toReal }
  change sSup S ≤ A + (1 + epsilon) * Kyprianou.Ch07.kestenSupEnvelope G n
  have hNonempty : S.Nonempty := by
    refine ⟨((Kyprianou.Ch07.convolutionPower G (n + 1))
      (Set.Ioi (1 : Real))).toReal / (G (Set.Ioi (1 : Real))).toReal, ?_⟩
    exact ⟨1, by norm_num, rfl⟩
  apply csSup_le hNonempty
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hPointwise n hn x hx
