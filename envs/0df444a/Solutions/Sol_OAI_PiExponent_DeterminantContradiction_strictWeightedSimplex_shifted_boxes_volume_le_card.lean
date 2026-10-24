-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_shifted_boxes_volume_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:26:06.45589+00:00
-- url     : https://prove2.me/submissions/f89d5a40-16b1-469e-a086-3ce39ed8594b

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (T : Real) :
    ENNReal.toReal
      (MeasureTheory.volume
        (⋃ a ∈ (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)),
          {x : Fin n → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}))
      ≤ ((strictWeightedSimplex w (T + Finset.univ.sum w)).card : Real) := by
  classical
  let S := strictWeightedSimplex w (T + Finset.univ.sum w)
  let B : (Fin n → Nat) → Set (Fin n → Real) :=
    fun a => {x | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}
  have hB (a : Fin n → Nat) :
      B a = Set.pi Set.univ (fun i => Set.Ico (a i : Real) ((a i : Real) + 1)) := by
    ext x
    simp [B, Set.mem_pi, Set.mem_Ico]
  have hvol (a : Fin n → Nat) : MeasureTheory.volume (B a) = 1 := by
    rw [hB, Real.volume_pi_Ico]
    simp
  have hle : MeasureTheory.volume (⋃ a ∈ S, B a) ≤ (S.card : ENNReal) := by
    calc
      MeasureTheory.volume (⋃ a ∈ S, B a)
          ≤ ∑ a ∈ S, MeasureTheory.volume (B a) :=
            MeasureTheory.measure_biUnion_finset_le (μ := MeasureTheory.volume) S B
      _ = (S.card : ENNReal) := by simp [hvol]
  have hreal := ENNReal.toReal_mono (by simp) hle
  have hcard : ENNReal.toReal (S.card : ENNReal) = (S.card : Real) := by simp
  rw [hcard] at hreal
  simpa [S, B] using hreal