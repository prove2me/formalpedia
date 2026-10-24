-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_eq_diagonalScaling_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:54.365193+00:00
-- url     : https://prove2.me/submissions/6bce82a6-46fa-49f0-9702-c2e350dda67a

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) :
    {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H} =
      Set.image (fun y : Fin m → Real => fun i => y i / w i)
        {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨fun i => w i * x i, ⟨fun i => mul_nonneg (hw i).le (hx i), hs⟩, ?_⟩
    ext i; field_simp [(hw i).ne']
  · rintro ⟨y, ⟨hy, hs⟩, rfl⟩
    refine ⟨fun i => div_nonneg (hy i) (hw i).le, ?_⟩
    have : ∀ i, w i * (y i / w i) = y i := fun i => by field_simp [(hw i).ne']
    simpa [this] using hs
