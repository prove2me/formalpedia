-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_full_fubini
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:05:43.403418+00:00
-- url     : https://prove2.me/submissions/b9960a69-4118-40ef-97f1-34290e9823a9

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem solution
    (n : Nat) (T : Real) :
    (∫⁻ t : Real,
      MeasureTheory.volume
        {y : Fin n → Real |
          0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}
      ∂MeasureTheory.volume) =
      MeasureTheory.volume
        {z : Real × (Fin n → Real) |
          0 ≤ z.1 ∧ (∀ i, 0 ≤ z.2 i) ∧
            z.1 + (∑ i, z.2 i) < T} := by
  let s : Set (Real × (Fin n → Real)) :=
    {z | 0 ≤ z.1 ∧ (∀ i, 0 ≤ z.2 i) ∧
      z.1 + (∑ i, z.2 i) < T}
  have hs : MeasurableSet s := by
    dsimp [s]
    measurability
  rw [MeasureTheory.Measure.volume_eq_prod Real (Fin n → Real)]
  rw [MeasureTheory.Measure.prod_apply hs]
  apply MeasureTheory.lintegral_congr
  intro t
  apply congrArg MeasureTheory.volume
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, s]
  constructor
  · rintro ⟨ht, hy, hsum⟩
    exact ⟨ht, hy, by linarith⟩
  · rintro ⟨ht, hy, hsum⟩
    exact ⟨ht, hy, by linarith⟩