-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_floor_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:07:46.44678+00:00
-- url     : https://prove2.me/submissions/44b23930-b523-41a6-b290-7520d660783c

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T)
    (x : Fin n → Real)
    (hx : (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T) :
    (∑ i, w i * ((Nat.floor (x i) : Nat) : Real)) < T := by
  rcases hx with ⟨hx_nonneg, hx_lt⟩
  calc
    (∑ i, w i * ((Nat.floor (x i) : Nat) : Real)) ≤ ∑ i, w i * x i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (hx_nonneg i)) (hw i).le
    _ < T := hx_lt