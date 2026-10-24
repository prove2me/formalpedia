-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:55.126448+00:00
-- url     : https://prove2.me/submissions/27175d67-9014-4a0f-bccf-2649a1a2f964

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib

open MeasureTheory Filter Topology in

theorem solution (n : Nat) (a : Real) (ha : 0 ≤ a) :
    {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
      (Finset.univ.sum fun i : Fin n => x i) ≤ a} =
    Set.image (fun y : Fin n → Real => fun i => a * y i)
      {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧
        (Finset.univ.sum fun i : Fin n => y i) ≤ 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hs⟩
    rcases ha.lt_or_eq with ha | ha
    · refine ⟨fun i => a⁻¹ * x i, ⟨fun i => mul_nonneg (inv_nonneg.2 ha.le) (hx i), ?_⟩, ?_⟩
      · rw [← Finset.mul_sum, inv_mul_le_iff₀ ha]; linarith
      · ext i; field_simp [ha.ne']
    · subst ha
      refine ⟨0, ⟨fun i => le_refl _, by simp⟩, ?_⟩
      have h0 : ∀ i ∈ Finset.univ, x i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).1
          (le_antisymm hs (Finset.sum_nonneg fun i _ => hx i))
      ext i; simp [h0 i (Finset.mem_univ _)]
  · rintro ⟨y, ⟨hy, hs⟩, rfl⟩
    refine ⟨fun i => mul_nonneg ha (hy i), ?_⟩
    rw [← Finset.mul_sum]; nlinarith
