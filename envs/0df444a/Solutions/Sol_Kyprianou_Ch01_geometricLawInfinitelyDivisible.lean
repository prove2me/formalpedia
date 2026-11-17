-- Prove2me | solution 1 for Kyprianou.Ch01.geometricLawInfinitelyDivisible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:40:53.469204+00:00
-- url     : https://prove2.me/submissions/b401bc91-565e-461c-9f16-2d9ed294438d

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_geometricLaw_eqMathlib
import Theorems.Thm_Kyprianou_Ch01_geometricMeasureInfinitelyDivisible
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (G : Measure ℕ) [IsProbabilityMeasure G]
    (hGeom : ∀ k : ℕ,
      G {k} = ENNReal.ofReal (p * (1 - p) ^ k)) :
    LevyFoundations.isInfinitelyDivisibleLaw
      (G.map (fun k : ℕ => (k : ℝ))) := by
  let q : unitInterval.Elem := ⟨p, ⟨le_of_lt hp0, hp1⟩⟩
  have hq : q ≠ 0 := by
    intro h
    have hpz : p = 0 := congrArg Subtype.val h
    exact (ne_of_gt hp0) hpz
  have hG := Kyprianou.Ch01.geometricLaw_eqMathlib p hp0 hp1 G hGeom
  change G = ProbabilityTheory.geometricMeasure q at hG
  rw [hG]
  exact Kyprianou.Ch01.geometricMeasureInfinitelyDivisible q hq
