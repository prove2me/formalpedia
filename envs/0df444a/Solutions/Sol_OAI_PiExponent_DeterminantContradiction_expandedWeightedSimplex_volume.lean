-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.expandedWeightedSimplex_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:29:38.397422+00:00
-- url     : https://prove2.me/submissions/8457affc-3649-4356-b734-de9a55097a5d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_preimage_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_normalization
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_measurable
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_arithmetic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_zeroDimensional_weightedSimplex_volume
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (H : Real) (hH : 0 ≤ H) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (∑ i, w i * x i) ≤ H + Finset.univ.sum w} =
      ENNReal.ofReal
        ((H + Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) := by
  by_cases hn : n = 0
  · subst n
    exact OAI.PiExponent.DeterminantContradiction.zeroDimensional_weightedSimplex_volume
      w hw H hH
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
    let B : Real := H + Finset.univ.sum w
    have hB : 0 < B := by
      dsimp [B]
      have hsum : 0 < Finset.univ.sum w :=
        Finset.sum_pos (fun i hi => hw i)
          (Finset.univ_nonempty_iff.mpr ‹Nonempty (Fin n)›)
      linarith
    rw [OAI.PiExponent.DeterminantContradiction.weightedSimplex_normalization
      n w hw B hB]
    change MeasureTheory.volume
        {x : Fin n → Real | (fun i => w i / B * x i) ∈
          ({y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} : Set (Fin n → Real))} = _
    rw [OAI.PiExponent.DeterminantContradiction.diagonal_preimage_volume
      n (fun i => w i / B) (fun i => div_pos (hw i) hB)
      {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1}
      (OAI.PiExponent.DeterminantContradiction.standardSimplex_measurable n)]
    rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_volume n]
    exact OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_arithmetic
      n w hw B hB
