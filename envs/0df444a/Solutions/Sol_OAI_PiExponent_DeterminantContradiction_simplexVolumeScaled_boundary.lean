-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:14:58.465272+00:00
-- url     : https://prove2.me/submissions/433adaa1-2ad3-4a0d-a70f-a1e562f9b9d7

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (n : Nat) (r : Real) (hr : 0 ≤ r)
    (hboundary : n = 0 ∨ r = 0) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n) * MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by
  rcases hboundary with hn | hr0
  · subst n
    simp [hr]
  · subst r
    cases n with
    | zero => simp
    | succ n =>
      have hset :
          {x : Fin (Nat.succ n) → Real |
            (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 0} =
            ({0} : Set (Fin (Nat.succ n) → Real)) := by
        ext x
        constructor
        · intro hx
          have hxzero : ∀ i, x i = 0 := by
            intro i
            have hle : x i ≤ ∑ j, x j :=
              Finset.single_le_sum (fun j hj => hx.1 j) (Finset.mem_univ i)
            exact le_antisymm (le_trans hle hx.2) (hx.1 i)
          ext i
          exact hxzero i
        · intro hx
          subst x
          simp
      rw [hset]
      simp
