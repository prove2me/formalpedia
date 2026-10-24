-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:04:13.310237+00:00
-- url     : https://prove2.me/submissions/13dab127-fb3c-4551-b0d8-cdbf066d1e7a

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (m : Nat) (s T : Real) (hs : 0 < s) (hT : 0 < T) :
    {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < s} =
      (fun x => (T / s) • x) ⁻¹' {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Pi.smul_apply]
  let c : Real := T / s
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos hT hs
  have hcs : c * s = T := by
    dsimp [c]
    exact div_mul_cancel₀ T (ne_of_gt hs)
  change ((∀ i, 0 ≤ x i) ∧ (∑ i, x i) < s) ↔
    ((∀ i, 0 ≤ c * x i) ∧ (∑ i, c * x i) < T)
  constructor
  · rintro ⟨hcoord, hsum⟩
    constructor
    · intro i
      exact mul_nonneg (le_of_lt hc) (hcoord i)
    · calc
        (∑ i, c * x i) = c * (∑ i, x i) := by rw [Finset.mul_sum]
        _ < c * s := mul_lt_mul_of_pos_left hsum hc
        _ = T := hcs
  · rintro ⟨hcoord, hsum⟩
    constructor
    · intro i
      have hi := hcoord i
      nlinarith [hc]
    · have hsum' : c * (∑ i, x i) < c * s := by
        calc
          c * (∑ i, x i) = (∑ i, c * x i) := by rw [Finset.mul_sum]
          _ < T := hsum
          _ = c * s := hcs.symm
      by_contra h
      have hsle : s ≤ ∑ i, x i := le_of_not_gt h
      have hmono : c * s ≤ c * (∑ i, x i) :=
        mul_le_mul_of_nonneg_left hsle (le_of_lt hc)
      linarith
