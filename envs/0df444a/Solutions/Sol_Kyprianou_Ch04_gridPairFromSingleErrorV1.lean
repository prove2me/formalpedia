-- Prove2me | solution 1 for Kyprianou.Ch04.gridPairFromSingleErrorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:36:37.464671+00:00
-- url     : https://prove2.me/submissions/68c4ceaf-da90-43cf-885c-1bc9b77b2208

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_gridPairErrorUnionV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A mesh-uniform one-cutoff probability estimate implies its cofinal two-cutoff version. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : NNReal)
    (A : ℕ → NNReal → Ω → ℝ) (B : ℕ → ℕ → NNReal → Ω → ℝ)
    (h : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, (P {w | ∃ t ≤ T, δ ≤ |B m n t w-A n t w|}).toReal ≤ η) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T,
        δ ≤ |B l n t w-B m n t w|}).toReal ≤ η := by
  apply Kyprianou.Ch04.gridPairErrorUnionV1 P T
    (fun m n l t w => B l n t w-A n t w) (fun m n l t w => A n t w-B m n t w)
    (fun m n l t w => B l n t w-B m n t w) (fun m n l t w => by ring)
  · intro δ hδ η hη
    exact Eventually.of_forall fun m n => (h δ hδ η hη).mono fun l hl => hl n
  · intro δ hδ η hη
    filter_upwards [h δ hδ η hη] with m hm
    intro n
    exact Eventually.of_forall fun l => by simpa only [abs_sub_comm] using hm n
