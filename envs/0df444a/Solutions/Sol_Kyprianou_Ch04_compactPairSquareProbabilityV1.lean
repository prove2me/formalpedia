-- Prove2me | solution 1 for Kyprianou.Ch04.compactPairSquareProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:44:21.671141+00:00
-- url     : https://prove2.me/submissions/8c558b8d-aba3-4419-9f9c-f0a5c9d81417

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A pair deviation in the product metric is controlled by its two coordinate events. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U U' V V' : NNReal → Ω → ℝ) (T : NNReal) (d p : ℝ) (hp : 0 ≤ p)
    (hu : P {w | ∃ t ≤ T, d < |U t w - U' t w|} ≤ ENNReal.ofReal (p/2))
    (hv : P {w | ∃ t ≤ T, d < |V t w - V' t w|} ≤ ENNReal.ofReal (p/2)) :
    P {w | ∃ t ≤ T, d < dist (U t w,V t w) (U' t w,V' t w)} ≤
      ENNReal.ofReal p := by
  let A := {w | ∃ t ≤ T, d < |U t w - U' t w|}
  let B := {w | ∃ t ≤ T, d < |V t w - V' t w|}
  have hsub : {w | ∃ t ≤ T, d < dist (U t w,V t w) (U' t w,V' t w)} ⊆ A ∪ B := by
    rintro w ⟨t,ht,h⟩
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,lt_max_iff] at h
    exact h.imp (fun h => ⟨t,ht,h⟩) (fun h => ⟨t,ht,h⟩)
  calc
    _ ≤ P (A ∪ B) := measure_mono hsub
    _ ≤ P A + P B := measure_union_le A B
    _ ≤ ENNReal.ofReal (p/2) + ENNReal.ofReal (p/2) := add_le_add hu hv
    _ = ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
