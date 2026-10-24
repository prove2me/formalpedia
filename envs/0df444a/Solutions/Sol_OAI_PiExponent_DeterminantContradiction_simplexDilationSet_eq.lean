-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexDilationSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:12.078977+00:00
-- url     : https://prove2.me/submissions/a21b2df8-facb-4283-8705-a603c9bc5d79

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution (n : Nat) (c : Real) (hc : 0 ≤ c) :
    {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin n, x i) ≤ c} =
      (fun x : Fin n → Real => c • x) ''
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin n, x i) ≤ 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hs⟩
    rcases hc.lt_or_eq with hc | hc
    · refine ⟨c⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hc.le) (hx i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ hc]; linarith
      · simp [smul_smul, hc.ne']
    · subst hc
      refine ⟨0, ⟨fun i => le_refl _, by simp⟩, ?_⟩
      have h0 : ∀ i ∈ Finset.univ, x i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).1
          (le_antisymm hs (Finset.sum_nonneg fun i _ => hx i))
      ext i; simp [h0 i (Finset.mem_univ _)]
  · rintro ⟨y, ⟨hy, hs⟩, rfl⟩
    refine ⟨fun i => mul_nonneg hc (hy i), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    nlinarith
