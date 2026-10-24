-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexSliceVolume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:52:49.661329+00:00
-- url     : https://prove2.me/submissions/92ed5df2-653f-4619-a11b-601d591b053d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexDilationVolume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume
open scoped BigOperators

theorem solution (n : Nat) (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1 - t} =
    ENNReal.ofReal (((1 - t) ^ n) / (Nat.factorial n : Real)) := by
  have hc : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  rw [OAI.PiExponent.DeterminantContradiction.simplexDilationVolume n (1 - t) hc,
    OAI.PiExponent.DeterminantContradiction.unitSimplexVolume]
  have hpow : ENNReal.ofReal ((1 - t) ^ n) = ENNReal.ofReal (1 - t) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          ENNReal.ofReal ((1 - t) ^ (n + 1)) =
              ENNReal.ofReal ((1 - t) ^ n * (1 - t)) := by rw [pow_succ]
          _ = ENNReal.ofReal ((1 - t) ^ n) * ENNReal.ofReal (1 - t) :=
            ENNReal.ofReal_mul (by positivity)
          _ = ENNReal.ofReal (1 - t) ^ n * ENNReal.ofReal (1 - t) := by rw [ih]
          _ = ENNReal.ofReal (1 - t) ^ (n + 1) := by rw [pow_succ]
  calc
    ENNReal.ofReal (1 - t) ^ n * ENNReal.ofReal (1 / (Nat.factorial n : Real)) =
        ENNReal.ofReal ((1 - t) ^ n) *
          ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by rw [← hpow]
    _ = ENNReal.ofReal ((1 - t) ^ n * (1 / (Nat.factorial n : Real))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (((1 - t) ^ n) / (Nat.factorial n : Real)) := by
      congr 1
      ring