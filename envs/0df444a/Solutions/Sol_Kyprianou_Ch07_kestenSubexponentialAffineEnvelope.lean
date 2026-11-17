-- Prove2me | solution 1 for Kyprianou.Ch07.kestenSubexponentialAffineEnvelope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:40:00.032271+00:00
-- url     : https://prove2.me/submissions/4a0e247c-527d-4a50-8394-de6a3837e23d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
import Theorems.Thm_Kyprianou_Ch07_kestenSupEnvelopeAffineStep
import Theorems.Thm_Kyprianou_Ch07_kestenSupEnvelopeFinite
import Theorems.Thm_Kyprianou_Ch07_kestenSupEnvelopeOne
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open Kyprianou.Ch07
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConvolutionAsymptotics : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ A B : Real, 0 ≤ A ∧ 0 ≤ B ∧
        ∃ xi : Nat → Real,
          xi 0 ≤ B ∧
          (∀ n : Nat, xi (n + 1) ≤ A + (1 + epsilon) * xi n) ∧
          ∀ n : Nat, 1 ≤ n →
            ∀ x : Real, 0 < x →
              ((convolutionPower G n) (Set.Ioi x)).toReal /
                (G (Set.Ioi x)).toReal ≤ xi n := by
  intro epsilon hEpsilon
  obtain ⟨A, hA, hStep⟩ :=
    Kyprianou.Ch07.kestenSupEnvelopeAffineStep
      G hPositiveTail hConvolutionAsymptotics epsilon hEpsilon
  let xi : Nat → Real := fun n =>
    if n = 0 then 0 else Kyprianou.Ch07.kestenSupEnvelope G n
  refine ⟨A, 0, by linarith, le_refl 0, xi, ?_, ?_, ?_⟩
  · simp [xi]
  · intro n
    by_cases hn : n = 0
    · subst n
      have hOne := Kyprianou.Ch07.kestenSupEnvelopeOne
        G hPositiveTail
      simpa [xi, hOne] using hA
    · have hnPos : 1 ≤ n := by omega
      simpa [xi, hn] using hStep n hnPos
  · intro n hn x hx
    obtain ⟨C, hC, hBound, hFinite⟩ :=
      Kyprianou.Ch07.kestenSupEnvelopeFinite
        G hPositiveTail hConvolutionAsymptotics n hn
    have hnNe : n ≠ 0 := by omega
    simpa [xi, hnNe] using hBound x hx
