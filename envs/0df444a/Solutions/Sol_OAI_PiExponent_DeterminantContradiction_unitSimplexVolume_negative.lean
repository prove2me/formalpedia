-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_negative
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:29:02.394976+00:00
-- url     : https://prove2.me/submissions/0656facf-c9e5-4656-a418-74a61ffb7af9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem solution
    (n : Nat) (c : Real) (hc : c < 0) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} = 0 := by
  have h_empty :
      ({x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} : Set (Fin n → Real)) = ∅ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨h_nonneg, h_le⟩
      have h_sum : 0 ≤ Finset.univ.sum (fun i : Fin n => x i) :=
        Finset.sum_nonneg (fun i hi => h_nonneg i)
      linarith
    · intro hx
      have h_false : False := by simpa using hx
      exact h_false.elim
  simp [h_empty]